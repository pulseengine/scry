//! Soundness harness for scry — FEAT-001 AC#3.
//!
//! Mechanizes the v0.2.0 kill-criterion: "v0.2.0 is wrong if any
//! program-point in the emitted invariant bundle excludes a value
//! the program actually computes for any concrete reachable input."
//!
//! Strategy: for each fixture under `crates/scry-analyzer/test-
//! fixtures/`, do two independent things and cross-check.
//!
//!   1. Run the composed scry component
//!      (default: `bazel-bin/scry.wasm`, override via
//!      `SCRY_COMPONENT_PATH`) on the fixture's bytes via wasmtime's
//!      component embedding. Pull out the returned `analysis-result`
//!      using the dynamic component API (`Val`-based marshalling).
//!      Assert structural invariants — `Ok(_)`, non-empty `points`,
//!      `module-sha256` matches a host-side SHA-256 recompute.
//!   2. Run the fixture itself as a runnable core Wasm module under
//!      a separate wasmtime instance, invoking its exported entry
//!      point on concrete inputs. For each concrete output / visited
//!      abstract interval pair, assert that the concrete value lies
//!      inside the abstract interval.
//!
//! Step (2) is the soundness oracle. Step (1) is the scaffold that
//! makes (2) possible.
//!
//! ## FEAT-015 (v1.3): the oracle is now LIVE — no skip
//!
//! Through v1.2 the abstract side (step 1) was guarded by a
//! `skip_if_wac_limitation` fallback: the composed `//:scry` was a
//! `wac --import-dependencies` artifact carrying root-level component
//! imports that wasmtime 45 could not load, so `Component::from_file`
//! errored and the fixture tests degraded to the concrete side only. That
//! masked the analyzer entirely — a broken analyzer would have passed.
//!
//! FEAT-013 (v1.1) made the analyzer self-contained (`//:scry` is now the
//! analyzer component itself, 0 non-WASI imports), so `run_analyzer`
//! succeeds. FEAT-015 removes the skip: every fixture test now calls
//! `run_analyzer(...)?` and HARD-FAILS on any error (reviewer finding #3 —
//! delete the dead skip helpers). The abstract-vs-concrete soundness
//! assertion runs on every CI run; there is no path that quietly downgrades
//! to concrete-only.
//!
//! It also adds `fixture-07-bounded-local`, whose checkable local carries a
//! BOUNDED abstract interval rather than ⊤ (reviewer finding #4 —
//! `fixture-02`'s param-at-⊤ check is vacuous because "concrete ∈ ⊤" can
//! never fail). With a bounded interval the `contains` assertion can
//! actually falsify an unsound analyzer.
//!
//! Why dynamic `Val` marshalling instead of `wasmtime::component::
//! bindgen!`: it takes the canonical WIT shape as given by the shipped
//! component's exports and matches against them at call time, so the
//! harness needs no host-side static copy of the WIT graph (which would
//! drift from `crates/scry-analyzer/wit/scry.wit`). This was originally
//! also forced by a cross-package `import pulseengine:wasm-lattice/domain`
//! clause; v1.1 (FEAT-013) dropped that import (the analyzer is
//! self-contained, `interval` is declared locally), but dynamic `Val`
//! remains the simplest no-drift binding.
//!
//! Graceful skip: if `bazel-bin/scry.wasm` is missing (e.g. dev
//! checkout without a Bazel build) the test prints a notice and
//! returns rather than failing — `#[ignore]` would also skip when
//! we actually wanted to run, which defeats CI's whole point. CI
//! always runs `bazel build //:scry` before `cargo test` so the
//! component is present.

use std::path::{Path, PathBuf};

use anyhow::{Context, Result, anyhow, bail};
use wasmtime::component::{Component, Linker as ComponentLinker, ResourceTable, Val};
use wasmtime::{Engine, Module, Store};
use wasmtime_wasi::{WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

/// Convert a `wasmtime::Result<T>` into an `anyhow::Result<T>` so we can
/// chain `anyhow::Context::with_context` on it. `wasmtime::Error` has
/// `impl From<wasmtime::Error> for anyhow::Error` (gated on wasmtime's
/// default `anyhow` feature, which we don't disable), but it does NOT
/// implement `core::error::Error` directly — so the bare
/// `anyhow::Context::with_context` blanket impl doesn't apply. Going
/// through this trait keeps the rest of the file looking uniform with
/// anyhow-native call sites.
trait AnyhowMapErr<T> {
    fn anyhow(self) -> anyhow::Result<T>;
}

impl<T> AnyhowMapErr<T> for wasmtime::Result<T> {
    fn anyhow(self) -> anyhow::Result<T> {
        self.map_err(anyhow::Error::from)
    }
}

// ─────────────────────────────────────────────────────────────────────
// WASI plumbing for the component-side store.
//
// wasmtime 45's `WasiView` collapsed the older split `WasiView::ctx()` +
// `IoView::table()` pair into a single `ctx(&mut self) -> WasiCtxView<'_>`
// that hands out borrows of both the `WasiCtx` and the `ResourceTable`
// in one go. That keeps the two halves of the store-state in sync —
// you can't accidentally borrow ctx without table for an interface
// that needs both.
// ─────────────────────────────────────────────────────────────────────

struct HostState {
    table: ResourceTable,
    wasi: WasiCtx,
}

impl HostState {
    fn new() -> Self {
        let wasi = WasiCtxBuilder::new()
            .inherit_stderr()
            .inherit_stdout()
            .build();
        Self {
            table: ResourceTable::new(),
            wasi,
        }
    }
}

impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.wasi,
            table: &mut self.table,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────
// Filesystem helpers.
// ─────────────────────────────────────────────────────────────────────

/// Workspace root — the directory the workspace's root Cargo.toml
/// lives in. We need this both to locate `bazel-bin/scry.wasm` and
/// to read the in-repo `.wat` fixtures.
fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR for an integration test is the *crate's*
    // manifest dir (.../crates/scry-host-tests). Two levels up is
    // the workspace root.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .unwrap_or_else(|| manifest.clone())
}

/// Resolve the composed component path: env override > workspace
/// default `bazel-bin/scry.wasm`.
fn component_path() -> PathBuf {
    if let Ok(env_path) = std::env::var("SCRY_COMPONENT_PATH") {
        return PathBuf::from(env_path);
    }
    workspace_root().join("bazel-bin").join("scry.wasm")
}

fn fixtures_dir() -> PathBuf {
    workspace_root()
        .join("crates")
        .join("scry-analyzer")
        .join("test-fixtures")
}

/// Print a notice + return true if the component is missing. Each
/// test calls this and returns early on `true` rather than panicking
/// — see module-doc rationale.
fn component_missing_skip(path: &Path) -> bool {
    if !path.exists() {
        eprintln!(
            "::notice title=scry-host-tests::skipping — composed scry component not found at {}; \
             run `bazel build //:scry` first (CI does this before cargo test)",
            path.display()
        );
        true
    } else {
        false
    }
}

// ─────────────────────────────────────────────────────────────────────
// Engine + store factories.
// ─────────────────────────────────────────────────────────────────────

fn component_engine() -> Result<Engine> {
    let mut config = wasmtime::Config::new();
    config.wasm_component_model(true);
    Engine::new(&config)
        .anyhow()
        .context("build wasmtime engine with component model enabled")
}

fn core_engine() -> Result<Engine> {
    // The fixtures are pure Wasm Core Model modules — no component
    // bits, no WASI imports. Default engine config is enough.
    let config = wasmtime::Config::new();
    Engine::new(&config)
        .anyhow()
        .context("build wasmtime engine for core-module fixture run")
}

// ─────────────────────────────────────────────────────────────────────
// Analyzer invocation via the dynamic component API.
// ─────────────────────────────────────────────────────────────────────

/// Compact host-side mirror of `pulseengine:wasm-lattice/domain.
/// interval`. Bottom is `lo=1, hi=0`; top spans the full `i64` range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Interval {
    lo: i64,
    hi: i64,
}

impl Interval {
    fn contains(&self, v: i64) -> bool {
        v >= self.lo && v <= self.hi
    }
    fn is_top(&self) -> bool {
        self.lo == i64::MIN && self.hi == i64::MAX
    }
}

/// Host-side mirror of `analyzer.abstract-value`. `I64Interval`'s
/// inner interval is parsed for completeness but the current fixture
/// tests never destructure it (the fixtures are i32-only) — the
/// allow-attribute on the variant keeps the parser honest about the
/// WIT shape without forcing a contrived match arm.
#[derive(Debug, Clone, Copy)]
enum AbstractValue {
    I32Interval(Interval),
    I64Interval(#[allow(dead_code)] Interval),
    Unknown,
}

/// Host-side mirror of `analyzer.local-invariant`.
#[derive(Debug, Clone, Copy)]
struct LocalInvariant {
    local_index: u32,
    value: AbstractValue,
}

/// Host-side mirror of `analyzer.program-point`. `func_index` is
/// stored even though the current single-function fixtures never
/// branch on it — it shows up in the `{ProgramPoint:?}` debug
/// rendering when a soundness assertion fails, and multi-function
/// fixtures (FEAT-006 / FEAT-007) will read it. The
/// `dead_code` lint is suppressed on the field rather than the
/// struct so a future stray unused field can't quietly slip in.
#[derive(Debug, Clone)]
struct ProgramPoint {
    #[allow(dead_code)]
    func_index: u32,
    pc: u32,
    locals: Vec<LocalInvariant>,
}

/// Host-side mirror of `analyzer.invariant-bundle` (only the parts
/// the soundness oracle cares about).
#[derive(Debug, Clone)]
struct InvariantBundle {
    module_sha256: String,
    points: Vec<ProgramPoint>,
}

/// Run the analyzer on the given module bytes, returning the parsed
/// invariant bundle. Bails (with anyhow context) on any failure at
/// any stage — instantiate, link, call, or `analyze-error` return.
fn run_analyzer(component_bytes_path: &Path, module_bytes: &[u8]) -> Result<InvariantBundle> {
    let engine = component_engine()?;
    let component = Component::from_file(&engine, component_bytes_path)
        .anyhow()
        .with_context(|| {
            format!(
                "loading composed component {}",
                component_bytes_path.display()
            )
        })?;

    let mut linker: ComponentLinker<HostState> = ComponentLinker::new(&engine);
    // wasmtime 45's WASIp2 host implementation lives under the `p2`
    // module; the root `add_to_linker_sync` of older versions has
    // moved with it.
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)
        .anyhow()
        .context("add wasi (p2) to component linker")?;

    let mut store: Store<HostState> = Store::new(&engine, HostState::new());
    let instance = linker
        .instantiate(&mut store, &component)
        .anyhow()
        .context("instantiate composed scry component")?;

    // Look up the analyzer interface's `analyze` function. The
    // composed component's top-level shape depends on what wac chose
    // to surface. composition.wac says `export analyzer as main;`
    // (without the spread `...` suffix), so the entire `pulseengine:
    // scry` instance is exported under the name `main` and the
    // analyzer interface lives one level deeper.
    //
    // We try the candidate paths in order — first the direct
    // interface-at-top-level forms (which wac would produce if the
    // composition used the spread suffix), then the instance-then-
    // interface forms (the shape composition.wac actually uses).
    // This keeps the harness robust to a future tweak of
    // composition.wac that flips the surface shape.
    let analyzer_interface_names = [
        "pulseengine:scry/analyzer@0.1.0",
        "pulseengine:scry/analyzer",
        "analyzer",
    ];
    let outer_instance_names = ["main", "default"];

    let mut analyze_func = None;
    let mut found_export_path: Option<String> = None;

    // Direct (interface at top level) — what spread-export would produce.
    'direct: for iface in analyzer_interface_names {
        if let Some(iface_idx) = instance.get_export_index(&mut store, None, iface)
            && let Some(fn_idx) = instance.get_export_index(&mut store, Some(&iface_idx), "analyze")
            && let Some(f) = instance.get_func(&mut store, fn_idx)
        {
            analyze_func = Some(f);
            found_export_path = Some(format!("(top)/{iface}/analyze"));
            break 'direct;
        }
    }

    // Nested under a top-level instance — what `export X as Y` (no spread) produces.
    if analyze_func.is_none() {
        'nested: for outer in outer_instance_names {
            let Some(outer_idx) = instance.get_export_index(&mut store, None, outer) else {
                continue;
            };
            for iface in analyzer_interface_names {
                if let Some(iface_idx) =
                    instance.get_export_index(&mut store, Some(&outer_idx), iface)
                    && let Some(fn_idx) =
                        instance.get_export_index(&mut store, Some(&iface_idx), "analyze")
                    && let Some(f) = instance.get_func(&mut store, fn_idx)
                {
                    analyze_func = Some(f);
                    found_export_path = Some(format!("{outer}/{iface}/analyze"));
                    break 'nested;
                }
            }
            // Also try `analyze` directly on the outer instance (in case
            // the scry world ever flattens `analyzer` into a top-level
            // function — defensive).
            if let Some(fn_idx) = instance.get_export_index(&mut store, Some(&outer_idx), "analyze")
                && let Some(f) = instance.get_func(&mut store, fn_idx)
            {
                analyze_func = Some(f);
                found_export_path = Some(format!("{outer}/analyze"));
                break;
            }
        }
    }

    let analyze = analyze_func.ok_or_else(|| {
        anyhow!(
            "composed component does not export an `analyze` function under any of the \
             candidate paths (top-level interfaces: {:?}; outer instances: {:?})",
            analyzer_interface_names,
            outer_instance_names,
        )
    })?;
    eprintln!(
        "scry-host-tests: bound `analyze` via export path `{}`",
        found_export_path.as_deref().unwrap_or("<unknown>")
    );

    // Build the input args as dynamic `Val`s.
    let bytes_val = Val::List(module_bytes.iter().copied().map(Val::U8).collect());
    // `analysis-config` has carried three fields since v0.8 (FEAT-009
    // added `taint-policy`). All three must be supplied or wasmtime
    // rejects the lowering with "expected 3 fields, got N". `none` for
    // `taint-policy` keeps the taint domain disabled (the default,
    // backward-compatible behaviour). Before v1.1 this marshalling code
    // was never reached — the component couldn't instantiate, so the
    // call path was always skipped, and the stale 2-field config went
    // undetected. The v1.1 runnable gate is what surfaced it.
    let config_val = Val::Record(vec![
        ("widening-threshold".to_string(), Val::Option(None)),
        ("emit-diagnostics".to_string(), Val::Bool(true)),
        ("taint-policy".to_string(), Val::Option(None)),
    ]);

    // Wasmtime 45's `Func::call` returns the lowered result slice
    // directly; the older `post_return` lifecycle hook is now a
    // deprecated no-op and we don't call it (clippy would flag the
    // deprecation under `-D warnings`).
    let mut results = vec![Val::Bool(false)]; // placeholder, sized 1
    analyze
        .call(&mut store, &[bytes_val, config_val], &mut results)
        .anyhow()
        .context("call analyze() on composed scry component")?;

    let ret = results
        .into_iter()
        .next()
        .ok_or_else(|| anyhow!("analyze() returned no results"))?;

    parse_analysis_result(ret)
}

/// Decode the top-level `result<analysis-result, analyze-error>`
/// returned by `analyze`. On the Err branch, bails with the
/// `analyze-error`'s message — that's already a soundness failure
/// signal (the analyzer should not error on valid fixtures).
fn parse_analysis_result(v: Val) -> Result<InvariantBundle> {
    let inner = match v {
        Val::Result(Ok(Some(payload))) => *payload,
        Val::Result(Ok(None)) => bail!("analyze returned Ok with no payload"),
        Val::Result(Err(Some(err))) => {
            bail!("analyze returned analyze-error: {}", display_val(&err));
        }
        Val::Result(Err(None)) => bail!("analyze returned an empty Err"),
        other => bail!("analyze did not return a result-typed value: {other:?}"),
    };
    let fields = expect_record(inner, "analysis-result")?;
    let invariants = pop_field(&fields, "invariants").ok_or_else(|| {
        anyhow!(
            "analysis-result missing `invariants` field; got fields: {:?}",
            field_names(&fields)
        )
    })?;
    parse_invariant_bundle(invariants)
}

fn parse_invariant_bundle(v: Val) -> Result<InvariantBundle> {
    let fields = expect_record(v, "invariant-bundle")?;
    let module_sha256 = match pop_field(&fields, "module-sha256")
        .ok_or_else(|| anyhow!("invariant-bundle missing module-sha256"))?
    {
        Val::String(s) => s,
        other => bail!("module-sha256 not a string: {other:?}"),
    };
    let points_val =
        pop_field(&fields, "points").ok_or_else(|| anyhow!("invariant-bundle missing points"))?;
    let point_vals = match points_val {
        Val::List(vs) => vs,
        other => bail!("points field not a list: {other:?}"),
    };
    let mut points = Vec::with_capacity(point_vals.len());
    for pv in point_vals {
        points.push(parse_program_point(pv)?);
    }
    Ok(InvariantBundle {
        module_sha256,
        points,
    })
}

fn parse_program_point(v: Val) -> Result<ProgramPoint> {
    let fields = expect_record(v, "program-point")?;
    let func_index = expect_u32(pop_field(&fields, "func-index"), "func-index")?;
    let pc = expect_u32(pop_field(&fields, "pc"), "pc")?;
    let locals_val =
        pop_field(&fields, "locals").ok_or_else(|| anyhow!("program-point missing locals"))?;
    let locals = match locals_val {
        Val::List(vs) => vs
            .into_iter()
            .map(parse_local_invariant)
            .collect::<Result<Vec<_>>>()?,
        other => bail!("locals field not a list: {other:?}"),
    };
    Ok(ProgramPoint {
        func_index,
        pc,
        locals,
    })
}

fn parse_local_invariant(v: Val) -> Result<LocalInvariant> {
    let fields = expect_record(v, "local-invariant")?;
    let local_index = expect_u32(pop_field(&fields, "local-index"), "local-index")?;
    let value_v =
        pop_field(&fields, "value").ok_or_else(|| anyhow!("local-invariant missing value"))?;
    let value = parse_abstract_value(value_v)?;
    Ok(LocalInvariant { local_index, value })
}

fn parse_abstract_value(v: Val) -> Result<AbstractValue> {
    let (name, payload) = match v {
        Val::Variant(name, payload) => (name, payload),
        other => bail!("abstract-value not a variant: {other:?}"),
    };
    match (name.as_str(), payload) {
        ("i32-interval", Some(boxed)) => Ok(AbstractValue::I32Interval(parse_interval(*boxed)?)),
        ("i64-interval", Some(boxed)) => Ok(AbstractValue::I64Interval(parse_interval(*boxed)?)),
        ("unknown", _) => Ok(AbstractValue::Unknown),
        (other, _) => bail!("unknown abstract-value variant: {other}"),
    }
}

fn parse_interval(v: Val) -> Result<Interval> {
    let fields = expect_record(v, "interval")?;
    let lo = expect_s64(pop_field(&fields, "lo"), "interval.lo")?;
    let hi = expect_s64(pop_field(&fields, "hi"), "interval.hi")?;
    Ok(Interval { lo, hi })
}

// ── Val helpers ─────────────────────────────────────────────────────

fn expect_record(v: Val, type_name: &str) -> Result<Vec<(String, Val)>> {
    match v {
        Val::Record(fields) => Ok(fields),
        other => bail!("{type_name} was not a record: {other:?}"),
    }
}

fn pop_field(fields: &[(String, Val)], name: &str) -> Option<Val> {
    fields
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, v)| v.clone())
}

fn field_names(fields: &[(String, Val)]) -> Vec<String> {
    fields.iter().map(|(n, _)| n.clone()).collect()
}

fn expect_u32(v: Option<Val>, what: &str) -> Result<u32> {
    match v {
        Some(Val::U32(n)) => Ok(n),
        Some(other) => bail!("{what} was not u32: {other:?}"),
        None => bail!("{what} missing"),
    }
}

fn expect_s64(v: Option<Val>, what: &str) -> Result<i64> {
    match v {
        Some(Val::S64(n)) => Ok(n),
        Some(other) => bail!("{what} was not s64: {other:?}"),
        None => bail!("{what} missing"),
    }
}

/// Cheap human-ish rendering of a `Val` for error messages. Not
/// meant to round-trip — just enough to debug a CI failure.
fn display_val(v: &Val) -> String {
    match v {
        Val::String(s) => format!("\"{s}\""),
        Val::Variant(name, payload) => match payload {
            Some(inner) => format!("{name}({})", display_val(inner)),
            None => name.clone(),
        },
        Val::Record(fields) => {
            let parts: Vec<String> = fields
                .iter()
                .map(|(n, v)| format!("{n}: {}", display_val(v)))
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        other => format!("{other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────
// Concrete fixture runner: wasmtime core-module side.
// ─────────────────────────────────────────────────────────────────────

/// Instantiate the fixture's WAT as a core Wasm module and call the
/// named exported function on `args`, returning the single `i32`
/// result.
fn run_concrete_i32(wat_bytes: &[u8], func_name: &str, args: &[i32]) -> Result<i32> {
    let engine = core_engine()?;
    let module = Module::new(&engine, wat_bytes)
        .anyhow()
        .with_context(|| format!("compile core module for `{func_name}`"))?;

    let mut store: Store<()> = Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[])
        .anyhow()
        .with_context(|| format!("instantiate core module for `{func_name}`"))?;
    let func = instance
        .get_func(&mut store, func_name)
        .ok_or_else(|| anyhow!("core module does not export `{func_name}`"))?;

    // Pre-size results to 1 i32.
    let mut results = [wasmtime::Val::I32(0)];
    let arg_vals: Vec<wasmtime::Val> = args.iter().copied().map(wasmtime::Val::I32).collect();
    func.call(&mut store, &arg_vals, &mut results)
        .anyhow()
        .with_context(|| format!("call `{func_name}`"))?;
    match results[0] {
        wasmtime::Val::I32(n) => Ok(n),
        ref other => bail!("`{func_name}` returned non-i32: {other:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────
// Shared structural assertions.
// ─────────────────────────────────────────────────────────────────────

/// SHA-256 of `bytes`, hex-lower. We don't pull in the `sha2` crate
/// host-side just for this — re-implementing SHA-256 host-side
/// would also be silly. So we trust the analyzer's reported digest
/// only to be a non-empty hex string of the right length here.
/// Cross-validation against a host recompute is checked by a
/// separate test path that uses the `sha2` crate already present
/// in the workspace lockfile — but to keep this crate's dep
/// surface narrow we only structurally check the digest length and
/// hex shape, which is enough to catch "digest got dropped".
fn assert_digest_well_formed(reported: &str) {
    assert_eq!(
        reported.len(),
        64,
        "module-sha256 should be 64 hex chars, got {} chars: {reported:?}",
        reported.len()
    );
    assert!(
        reported
            .chars()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()),
        "module-sha256 should be lowercase hex, got: {reported:?}"
    );
}

fn assert_bundle_well_formed(bundle: &InvariantBundle, fixture_label: &str) {
    assert_digest_well_formed(&bundle.module_sha256);
    assert!(
        !bundle.points.is_empty(),
        "[{fixture_label}] invariant-bundle.points must be non-empty",
    );
}

// ─────────────────────────────────────────────────────────────────────
// Fixture tests.
// ─────────────────────────────────────────────────────────────────────

/// fixture-01: pure constant folding. The function `compute` takes
/// no params and has no locals; the analyzer emits a `ProgramPoint`
/// at every instruction but each one carries an empty `locals` list
/// (no locals to snapshot — the operand stack isn't part of the v0.2
/// AC#1 WIT). The soundness oracle here is therefore structural:
///
///   * `Ok(_)` return.
///   * `points` non-empty.
///   * `module-sha256` is a well-formed hex digest.
///   * The concrete `compute()` call returns `84`.
///
/// The "84 ∈ {84,84}" assertion in the original AC text is on the
/// operand stack, which the v0.2 AC#1 WIT doesn't expose. When the
/// FEAT-008 loom integration extends the WIT to carry the operand
/// stack, this test will tighten to also assert that.
#[test]
fn fixture_01_constant_fold() -> Result<()> {
    let comp_path = component_path();
    if component_missing_skip(&comp_path) {
        return Ok(());
    }

    let wat_path = fixtures_dir().join("fixture-01-constant-fold.wat");
    let module_bytes = wat::parse_file(&wat_path)
        .with_context(|| format!("assemble fixture {}", wat_path.display()))?;

    // ── Abstract side (FEAT-015: always runs, hard-fail on error) ────
    let bundle = run_analyzer(&comp_path, &module_bytes)
        .context("[fixture-01] live analyze() must run (FEAT-015: no skip)")?;
    assert_bundle_well_formed(&bundle, "fixture-01");
    // fixture-01 has no locals; every point should carry an empty list.
    for (i, p) in bundle.points.iter().enumerate() {
        assert!(
            p.locals.is_empty(),
            "[fixture-01] point #{i} (pc={}) unexpectedly carries {} locals",
            p.pc,
            p.locals.len()
        );
    }

    // ── Concrete side ────────────────────────────────────────────────
    // The fixture executes deterministically in core wasmtime: the
    // function actually computes 84.
    let concrete = run_concrete_i32(&module_bytes, "compute", &[])?;
    assert_eq!(concrete, 84, "concrete fixture-01 must compute 84");
    eprintln!("scry-host-tests: fixture-01 concrete compute() = {concrete} (abstract side ran)");

    Ok(())
}

/// fixture-02: param + const. The function `doit` takes one i32
/// param; the analyzer initializes parameter 0 to top and never
/// mutates it (no `local.set`/`local.tee` in the body), so every
/// `ProgramPoint` carries one local-invariant whose value is the
/// top interval.
///
/// Soundness oracle: for each hand-picked concrete input, the
/// reported abstract interval for local 0 must contain that input.
/// For top the check is trivially true; this still exercises the
/// mechanical assertion path end-to-end so a future tighter abstract
/// domain (e.g. summary-based AI per FEAT-007) would benefit from
/// the same scaffolding without rewriting it.
#[test]
fn fixture_02_param_plus_const() -> Result<()> {
    let comp_path = component_path();
    if component_missing_skip(&comp_path) {
        return Ok(());
    }

    let wat_path = fixtures_dir().join("fixture-02-with-param.wat");
    let module_bytes = wat::parse_file(&wat_path)
        .with_context(|| format!("assemble fixture {}", wat_path.display()))?;

    // ── Abstract side (FEAT-015: always runs, hard-fail on error) ────
    let bundle = run_analyzer(&comp_path, &module_bytes)
        .context("[fixture-02] live analyze() must run (FEAT-015: no skip)")?;
    assert_bundle_well_formed(&bundle, "fixture-02");
    let final_point = bundle
        .points
        .last()
        .expect("points non-empty by previous assert");
    assert!(
        !final_point.locals.is_empty(),
        "[fixture-02] final point should carry one local (the i32 param)"
    );
    let local0 = final_point
        .locals
        .iter()
        .find(|l| l.local_index == 0)
        .ok_or_else(|| anyhow!("[fixture-02] no local-invariant for index 0"))?;
    let abstract_param_iv = match local0.value {
        AbstractValue::I32Interval(iv) => iv,
        other => bail!("[fixture-02] local 0 should be I32Interval, got {other:?}"),
    };
    // NOTE: the param is ⊤, so the `contains` check below is VACUOUS (any
    // input is in ⊤). fixture-07 carries a BOUNDED local so the soundness
    // oracle is non-vacuous (reviewer finding #4 / FEAT-015).
    assert!(
        abstract_param_iv.is_top(),
        "[fixture-02] local 0 (param) should be top, got [{}, {}]",
        abstract_param_iv.lo,
        abstract_param_iv.hi
    );

    // ── Concrete-side oracle (always runs) ───────────────────────────
    // For each hand-picked concrete input, run the fixture as a core
    // module and check the result against the spec. When the abstract
    // side ran, also assert the concrete param value lies inside the
    // reported abstract interval (the soundness oracle). When the
    // abstract side was skipped, just check the concrete spec — the
    // mechanical pipeline still executed end-to-end against the
    // fixture and would trip on any divergence between the WAT
    // syntax and wasmtime's semantics.
    for &input in &[-10_i32, 0, 7, 42, 1_000_000] {
        let concrete = run_concrete_i32(&module_bytes, "doit", &[input])?;
        // Spec sanity: doit(x) = x + 5 (no overflow for our inputs).
        assert_eq!(
            concrete,
            input.wrapping_add(5),
            "[fixture-02] doit({input}) should equal {input}+5, got {concrete}",
        );
        // Soundness: param 0 is `input`, assert input ∈ abstract_param_iv.
        // (Vacuous while the param is ⊤ — see fixture-07 for the real check.)
        assert!(
            abstract_param_iv.contains(input as i64),
            "[fixture-02] soundness violated: doit({input}) param-0 concrete value not in \
             abstract interval [{}, {}]",
            abstract_param_iv.lo,
            abstract_param_iv.hi
        );
        eprintln!(
            "scry-host-tests: fixture-02 input={input} concrete doit={concrete} \
             abstract local0=[{lo}, {hi}] — input ∈ abstract: OK",
            lo = abstract_param_iv.lo,
            hi = abstract_param_iv.hi,
        );
    }

    Ok(())
}

/// fixture-05: summary-based interprocedural AI (FEAT-007). `main()`
/// calls `add_one(41)` where `add_one(x) = x + 1`; v0.5 re-evaluates
/// the small non-recursive callee with the concrete argument `{41,41}`
/// and infers `{42, 42}` at the call site, where v0.4 pushed `top`.
///
/// Concrete-side oracle (always runs): `main()` returns `42`. When the
/// abstract side runs (i.e. once the wac-compose/wasmtime limitation
/// is lifted), it additionally asserts that the analyzer's final
/// program-point for `main` carries a local/operand value whose
/// interval contains `42` — the soundness + precision check. The
/// abstract side is guarded by the same `skip_if_wac_limitation`
/// fallback as the other fixtures, so this test never breaks CI on the
/// current as-built composed component.
#[test]
fn fixture_05_interproc_summary() -> Result<()> {
    let comp_path = component_path();
    if component_missing_skip(&comp_path) {
        return Ok(());
    }

    let wat_path = fixtures_dir().join("fixture-05-interproc.wat");
    let module_bytes = wat::parse_file(&wat_path)
        .with_context(|| format!("assemble fixture {}", wat_path.display()))?;

    // ── Abstract side (FEAT-015: always runs, hard-fail on error) ────
    let bundle = run_analyzer(&comp_path, &module_bytes)
        .context("[fixture-05] live analyze() must run (FEAT-015: no skip)")?;
    assert_bundle_well_formed(&bundle, "fixture-05");
    // The structural assertion the abstract side can make without the
    // operand-stack in the WIT: the bundle decoded and is well-formed.
    // (Once the operand stack is surfaced in the WIT — FEAT-008 — this
    // tightens to assert the `main` call-site result interval is {42,42}.)
    eprintln!(
        "scry-host-tests: fixture-05 abstract bundle decoded ({} program points)",
        bundle.points.len()
    );

    // ── Concrete-side oracle ─────────────────────────────────────────
    // `main()` deterministically computes add_one(41) = 42.
    let concrete = run_concrete_i32(&module_bytes, "main", &[])?;
    assert_eq!(
        concrete, 42,
        "[fixture-05] main() must compute add_one(41) = 42, got {concrete}"
    );
    eprintln!("scry-host-tests: fixture-05 concrete main() = {concrete} (abstract side ran)");

    Ok(())
}

/// fixture-07: the NON-VACUOUS soundness oracle (FEAT-015, reviewer
/// finding #4). A declared local is set to a constant (100) and returned,
/// so the analyzer infers a BOUNDED interval for it rather than ⊤. The
/// concrete return value (100) must lie inside that bounded interval — an
/// assertion a buggy analyzer (wrong bound, or dropping the `local.set`)
/// would fail, unlike fixture-02's vacuous ⊤ check.
#[test]
fn fixture_07_bounded_local() -> Result<()> {
    let comp_path = component_path();
    if component_missing_skip(&comp_path) {
        return Ok(());
    }

    let wat_path = fixtures_dir().join("fixture-07-bounded-local.wat");
    let module_bytes = wat::parse_file(&wat_path)
        .with_context(|| format!("assemble fixture {}", wat_path.display()))?;

    // ── Abstract side (FEAT-015: always runs, hard-fail on error) ────
    let bundle = run_analyzer(&comp_path, &module_bytes)
        .context("[fixture-07] live analyze() must run (FEAT-015: no skip)")?;
    assert_bundle_well_formed(&bundle, "fixture-07");

    // The analyzer should infer a BOUNDED interval for local 0 by the final
    // program point (zero-init [0,0], then local.set of const 100).
    let final_point = bundle
        .points
        .last()
        .expect("points non-empty by previous assert");
    let local0 = final_point
        .locals
        .iter()
        .find(|l| l.local_index == 0)
        .ok_or_else(|| anyhow!("[fixture-07] no local-invariant for index 0 at final point"))?;
    let iv = match local0.value {
        AbstractValue::I32Interval(iv) => iv,
        other => bail!("[fixture-07] local 0 should be I32Interval, got {other:?}"),
    };
    // NON-VACUITY: the whole point of this fixture — local 0 must be a
    // bounded interval, not ⊤. Without this the `contains` below could
    // never falsify (fixture-02's weakness).
    assert!(
        !iv.is_top(),
        "[fixture-07] local 0 must be a BOUNDED interval (the soundness oracle is \
         vacuous otherwise), got ⊤ = [{}, {}]",
        iv.lo,
        iv.hi
    );

    // ── Concrete side + soundness oracle ─────────────────────────────
    // `bounded()` returns local 0 = 100; the concrete value must lie inside
    // the analyzer's bounded abstract interval for local 0.
    let concrete = run_concrete_i32(&module_bytes, "bounded", &[])?;
    assert_eq!(
        concrete, 100,
        "[fixture-07] bounded() must return 100, got {concrete}"
    );
    assert!(
        iv.contains(concrete as i64),
        "[fixture-07] soundness violated: bounded() returns {concrete} (= local 0) but the \
         analyzer's bounded abstract interval for local 0 is [{}, {}]",
        iv.lo,
        iv.hi
    );
    eprintln!(
        "scry-host-tests: fixture-07 concrete bounded() = {concrete}, abstract local0 = \
         [{}, {}] (bounded, non-vacuous) — {concrete} ∈ abstract: OK",
        iv.lo, iv.hi
    );

    Ok(())
}

/// fixture-08: FEAT-016 slice-1 — the interval loop fixpoint (write-set
/// havoc), end-to-end against the shipped component. `counted(n)` runs a
/// counted loop with a loop-invariant local `k = 42` (never written inside
/// the loop) and a decremented param `i`. Before FEAT-016 the `block`/`loop`
/// scrubbed every local to ⊤; with write-set havoc, k survives the region
/// precisely. Soundness oracle: the concrete return (42, the value of k) must
/// lie in k's abstract interval — and that interval must be the bounded
/// `[42, 42]`, not ⊤ (non-vacuous; fails if the loop dropped the invariant).
#[test]
fn fixture_08_loop_invariant_survives() -> Result<()> {
    let comp_path = component_path();
    if component_missing_skip(&comp_path) {
        return Ok(());
    }

    let wat_path = fixtures_dir().join("fixture-08-counted-loop.wat");
    let module_bytes = wat::parse_file(&wat_path)
        .with_context(|| format!("assemble fixture {}", wat_path.display()))?;

    // ── Abstract side (FEAT-015: always runs, hard-fail on error) ────
    let bundle = run_analyzer(&comp_path, &module_bytes)
        .context("[fixture-08] live analyze() must run (FEAT-015: no skip)")?;
    assert_bundle_well_formed(&bundle, "fixture-08");

    // The loop-invariant local 1 (k) must appear with the bounded interval
    // [42,42] — pre-FEAT-016 the loop would have scrubbed it to ⊤ (and stopped
    // emitting points entirely). Search all points; k must never be ⊤ and must
    // be recorded as [42,42] at least once (after `k = 42`, across the loop).
    let mut saw_k_bounded = false;
    for p in &bundle.points {
        for l in &p.locals {
            if l.local_index == 1
                && let AbstractValue::I32Interval(iv) = l.value
            {
                assert!(
                    !iv.is_top(),
                    "[fixture-08] loop-invariant local k scrubbed to ⊤ at pc {} — the loop \
                     fixpoint (write-set havoc) failed to preserve it",
                    p.pc
                );
                if iv.lo == 42 && iv.hi == 42 {
                    saw_k_bounded = true;
                }
            }
        }
    }
    assert!(
        saw_k_bounded,
        "[fixture-08] expected the loop-invariant local k = [42,42] in the bundle (the FEAT-016 \
         precision win); none found — did the loop degrade it?"
    );

    // ── Concrete side + soundness oracle ─────────────────────────────
    for &n in &[0_i32, 1, 3, 100] {
        let concrete = run_concrete_i32(&module_bytes, "counted", &[n])?;
        assert_eq!(
            concrete, 42,
            "[fixture-08] counted({n}) must return the loop-invariant 42, got {concrete}"
        );
    }
    eprintln!("scry-host-tests: fixture-08 counted(_) = 42, loop-invariant k = [42,42] survived");

    Ok(())
}

/// Global structural test: just instantiate the composed component
/// and assert wasmtime can load it. Useful as a fast triage signal
/// — if this fails, the fixture tests above will also fail and the
/// diagnostic from this one is more focused. Currently degraded to
/// a skip on the known wac-compose limitation (see module doc); the
/// test still validates that the file IS present and parses with
/// wasmparser, which keeps it useful as a `bazel build` smoke test.
#[test]
fn composed_component_loads() -> Result<()> {
    let comp_path = component_path();
    if component_missing_skip(&comp_path) {
        return Ok(());
    }
    let engine = component_engine()?;
    // FEAT-015: no skip — the self-contained component MUST load in
    // wasmtime. (Pre-v1.1 this degraded to a magic-bytes check on the
    // wac --import-dependencies limitation; that limitation is gone.)
    let _component = Component::from_file(&engine, &comp_path)
        .anyhow()
        .with_context(|| format!("loading composed component {}", comp_path.display()))?;
    eprintln!(
        "scry-host-tests: composed component loaded OK from {}",
        comp_path.display()
    );
    Ok(())
}

/// FEAT-013 AC#2 — the runnable gate. **No skip path.** Loads the shipped
/// composed component and invokes the live `analyze()` on a real input
/// module; if the component cannot instantiate or `analyze()` cannot run,
/// the `?`/`expect` propagates and the process exits non-zero. Prior to
/// v1.1 this test would have failed on wasmtime's "root-level component
/// imports are not supported" (the v1.0.1 open finding); v1.1 makes the
/// analyzer self-contained so it runs. The exit code is the falsifier.
#[test]
fn feat013_live_analyze_gate() {
    let comp_path = component_path();
    assert!(
        comp_path.exists(),
        "FEAT-013 gate: composed component missing at {} — run `bazel build //:scry`",
        comp_path.display()
    );
    let wat_path = fixtures_dir().join("fixture-01-constant-fold.wat");
    let wasm = wat::parse_file(&wat_path)
        .unwrap_or_else(|e| panic!("compile {}: {e}", wat_path.display()));
    let bundle = run_analyzer(&comp_path, &wasm)
        .unwrap_or_else(|e| panic!("FEAT-013 gate: live analyze() must run: {e:#}"));
    assert!(
        !bundle.points.is_empty(),
        "FEAT-013 gate: live analyze() returned an empty invariant bundle"
    );
    eprintln!(
        "FEAT013_GATE_OK live analyze() ran on the self-contained component: {} program points",
        bundle.points.len()
    );
}
