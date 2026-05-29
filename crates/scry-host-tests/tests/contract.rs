//! Contract test for the scry invariant JSON schema — FEAT-008.
//!
//! This is the mechanical check that the published JSON contract
//! (`contracts/scry-invariants-v1.schema.json`) is a faithful, tight
//! description of scry's `analysis-result`. It is pure native — plain
//! serde structs + `serde_json` + the `jsonschema` crate — with no
//! wasmtime / component model involved, so it runs under `cargo test`
//! even though the component-loading tests in `tests/soundness.rs` skip
//! on the wac-compose/wasmtime limitation.
//!
//! Why plain serde structs (not the WIT bindings): the whole point of
//! FEAT-008 is that loom consumes the JSON contract WITHOUT coupling to
//! scry's WIT. So the contract has to stand on its own as a JSON shape.
//! We therefore define independent serde structs here that mirror the
//! WIT `analysis-result` (`crates/scry-analyzer/wit/scry.wit`),
//! serialize a representative value, and validate it against the schema.
//! If the schema and the WIT shape ever drift, this test fails.
//!
//! The representative value deliberately exercises all three loom
//! transforms the contract is meant to unlock (see
//! `docs/invariant-schema-v1.md`):
//!
//!   * a singleton interval (`{84,84}`)              -> constant-fold
//!   * a region-pointer with a bounded offset         -> bounds-check elision
//!   * a singleton, `sound` call-edge target set      -> devirtualize
//!
//! Honest constraint: this is a HAND-CONSTRUCTED value, not the output
//! of a live `analyze()` call. CI cannot drive a live analyze->JSON
//! round-trip because the composed component uses wac
//! `--import-dependencies` (root-level component imports) that wasmtime
//! 45 rejects — see the module doc in `tests/soundness.rs`. The v0.6.0
//! deliverable is the contract plus this mechanical validation.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use serde::Serialize;
use serde_json::Value;

// ── Serde mirror of the WIT `analysis-result` ───────────────────────
// All structs rename to kebab-case so the serialized JSON matches the
// WIT field names verbatim (which is what the schema keys on).

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct AnalysisResult {
    invariants: InvariantBundle,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    diagnostics: Vec<Diagnostic>,
    call_graph: Vec<CallEdge>,
    function_summaries: Vec<FunctionSummary>,
    // FEAT-002: optional in the contract (WIT `option<component-provenance>`).
    // Skipped when None so a v0.6-shaped document still validates.
    #[serde(skip_serializing_if = "Option::is_none")]
    provenance: Option<ComponentProvenance>,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct InvariantBundle {
    schema: String,
    module_sha256: String,
    points: Vec<ProgramPoint>,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct ProgramPoint {
    func_index: u32,
    pc: u32,
    locals: Vec<LocalInvariant>,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct LocalInvariant {
    local_index: u32,
    value: AbstractValue,
}

/// WIT `variant abstract-value` -> `kind`-tagged JSON union.
/// `#[serde(tag = "kind", rename_all = "kebab-case")]` produces
/// `{"kind":"i32-interval","interval":{...}}` etc., matching the schema.
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum AbstractValue {
    I32Interval { interval: Interval },
    I64Interval { interval: Interval },
    RegionPointer { region: Region },
    Unknown,
}

#[derive(Serialize)]
struct Interval {
    lo: i64,
    hi: i64,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct Region {
    region_id: u32,
    offset: Interval,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct Diagnostic {
    severity: String,
    func_index: u32,
    pc: u32,
    message: String,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct CallEdge {
    caller_func: u32,
    pc: u32,
    indirect: bool,
    resolved_targets: Vec<u32>,
    soundness: String,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct FunctionSummary {
    func_index: u32,
    param_count: u32,
    result_summary: Vec<AbstractValue>,
    context_sensitive: bool,
    recursive: bool,
}

/// FEAT-002 — serde mirror of WIT `component-provenance` / `component-origin`.
#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct ComponentProvenance {
    origins: Vec<ComponentOrigin>,
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
struct ComponentOrigin {
    fused_func_index: u32,
    component_id: u32,
    orig_func_index: u32,
}

// ── Schema location + representative value ───────────────────────────

const SCHEMA_ID: &str = "https://pulseengine.eu/scry-invariants/v1";

/// Path to the published contract, relative to the workspace root
/// (two levels up from this crate's manifest dir).
fn schema_path() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .unwrap_or_else(|| manifest.clone());
    workspace_root
        .join("contracts")
        .join("scry-invariants-v1.schema.json")
}

fn load_schema() -> Value {
    let path = schema_path();
    let bytes =
        std::fs::read(&path).unwrap_or_else(|e| panic!("read schema {}: {e}", path.display()));
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("parse schema {} as JSON: {e}", path.display()))
}

/// A representative `analysis-result` that exercises every kind in the
/// contract and all three loom-transform shapes.
fn representative_result() -> AnalysisResult {
    AnalysisResult {
        invariants: InvariantBundle {
            schema: SCHEMA_ID.to_string(),
            module_sha256: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
                .to_string(),
            points: vec![
                ProgramPoint {
                    func_index: 0,
                    pc: 12,
                    locals: vec![
                        LocalInvariant {
                            local_index: 0,
                            value: AbstractValue::I32Interval {
                                interval: Interval { lo: 0, hi: 42 },
                            },
                        },
                        // region-pointer -> bounds-check elision shape.
                        LocalInvariant {
                            local_index: 1,
                            value: AbstractValue::RegionPointer {
                                region: Region {
                                    region_id: 0,
                                    offset: Interval { lo: 0, hi: 16 },
                                },
                            },
                        },
                    ],
                },
                ProgramPoint {
                    func_index: 0,
                    pc: 40,
                    locals: vec![
                        // singleton interval {84,84} -> constant-fold shape.
                        LocalInvariant {
                            local_index: 0,
                            value: AbstractValue::I32Interval {
                                interval: Interval { lo: 84, hi: 84 },
                            },
                        },
                        LocalInvariant {
                            local_index: 1,
                            value: AbstractValue::Unknown,
                        },
                        LocalInvariant {
                            local_index: 2,
                            value: AbstractValue::I64Interval {
                                interval: Interval { lo: -1, hi: 100 },
                            },
                        },
                    ],
                },
            ],
        },
        diagnostics: vec![Diagnostic {
            severity: "info".to_string(),
            func_index: 0,
            pc: 4,
            message: "analyzed".to_string(),
        }],
        call_graph: vec![
            // singleton sound target set -> devirtualize shape.
            CallEdge {
                caller_func: 0,
                pc: 28,
                indirect: true,
                resolved_targets: vec![3],
                soundness: "sound".to_string(),
            },
            CallEdge {
                caller_func: 1,
                pc: 9,
                indirect: true,
                resolved_targets: vec![3, 4, 5],
                soundness: "unsound-fallback".to_string(),
            },
        ],
        function_summaries: vec![
            FunctionSummary {
                func_index: 0,
                param_count: 1,
                result_summary: vec![AbstractValue::I32Interval {
                    interval: Interval { lo: 84, hi: 84 },
                }],
                context_sensitive: true,
                recursive: false,
            },
            FunctionSummary {
                func_index: 3,
                param_count: 0,
                result_summary: vec![AbstractValue::Unknown],
                context_sensitive: false,
                recursive: true,
            },
        ],
        // FEAT-002: a decoded component-provenance map attributing two
        // fused functions to their originating components.
        provenance: Some(ComponentProvenance {
            origins: vec![
                ComponentOrigin {
                    fused_func_index: 0,
                    component_id: 0,
                    orig_func_index: 0,
                },
                ComponentOrigin {
                    fused_func_index: 3,
                    component_id: 1,
                    orig_func_index: 1,
                },
            ],
        }),
    }
}

/// Compile the published contract into a validator.
///
/// Uses `jsonschema::JSONSchema::compile`, the default-feature
/// constructor that is stable across the pinned 0.18.x line (the
/// crate-root `validator_for` / `Validator` re-exports are gated behind
/// the optional `resolve-*` features, so we avoid them). Validity is
/// then driven through `JSONSchema::is_valid` (`&Value -> bool`), which
/// needs no extra features and no version-specific error types.
#[allow(deprecated)]
fn compile() -> jsonschema::JSONSchema {
    let schema = load_schema();
    jsonschema::JSONSchema::compile(&schema)
        .unwrap_or_else(|e| panic!("compile scry-invariants v1 schema: {e}"))
}

// ─────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────

/// The schema document itself compiles as a JSON Schema validator and
/// declares draft 2020-12 with the v1 `$id`. This catches a malformed
/// schema before any instance check runs.
#[test]
fn schema_is_well_formed_draft_2020_12() {
    let schema = load_schema();
    assert_eq!(
        schema.get("$schema").and_then(Value::as_str),
        Some("https://json-schema.org/draft/2020-12/schema"),
        "contract must declare the draft 2020-12 dialect"
    );
    assert_eq!(
        schema.get("$id").and_then(Value::as_str),
        Some(SCHEMA_ID),
        "contract $id must be the v1 invariant URI"
    );
    // Compiling is the real well-formedness check.
    let _ = compile();
}

/// A representative `analysis-result`-shaped value, serialized via
/// serde_json, validates against the published v1 schema. This is the
/// mechanical check that the JSON contract stands alone for loom.
#[test]
fn representative_result_validates_against_schema() {
    let validator = compile();
    let instance =
        serde_json::to_value(representative_result()).expect("serialize representative result");

    assert!(
        validator.is_valid(&instance),
        "representative analysis-result must be valid against the v1 contract; \
         serialized value:\n{}",
        serde_json::to_string_pretty(&instance).unwrap_or_default()
    );
}

/// The three loom-transform shapes are present and well-formed in the
/// representative value:
///   * singleton interval {84,84}       -> constant-fold
///   * region-pointer w/ bounded offset -> bounds-check elision
///   * singleton sound call-edge        -> devirtualize
#[test]
fn loom_transform_shapes_present_and_valid() {
    let validator = compile();
    let instance = serde_json::to_value(representative_result()).expect("serialize");
    assert!(
        validator.is_valid(&instance),
        "instance must validate first"
    );

    // singleton interval (lo == hi) at the final program point.
    let last_point = &instance["invariants"]["points"][1];
    let local0 = &last_point["locals"][0]["value"];
    assert_eq!(local0["kind"], "i32-interval");
    assert_eq!(
        local0["interval"]["lo"], local0["interval"]["hi"],
        "constant-fold shape: local 0 at pc 40 must be a singleton interval"
    );

    // region-pointer with a bounded offset interval.
    let region_val = &instance["invariants"]["points"][0]["locals"][1]["value"];
    assert_eq!(region_val["kind"], "region-pointer");
    assert!(
        region_val["region"]["offset"]["hi"].is_i64(),
        "bounds-check-elision shape: region-pointer must carry an offset interval"
    );

    // singleton, sound call-edge.
    let edge0 = &instance["call-graph"][0];
    assert_eq!(edge0["soundness"], "sound");
    assert_eq!(
        edge0["resolved-targets"].as_array().map(Vec::len),
        Some(1),
        "devirtualize shape: a sound call-edge with a singleton target set"
    );
}

/// The contract is tight: structurally-broken instances are rejected.
/// This guards against an accidentally-permissive schema (e.g. dropping
/// `additionalProperties: false` or the `oneOf` discriminator).
///
/// `clippy::no_effect` is allowed: clippy (Rust 1.96+) false-positives on
/// the `bad[index] = serde_json::json!(..)` assignment statements — the
/// `IndexMut` assignment mutates `bad`, but the lint flags the `json!`
/// macro expansion as effect-free.
#[test]
#[allow(clippy::no_effect)]
fn schema_rejects_malformed_instances() {
    let validator = compile();

    // Base valid instance as mutable JSON.
    let mut base = serde_json::to_value(representative_result()).expect("serialize");
    assert!(validator.is_valid(&base), "base must be valid");

    // 1. abstract-value with a bad `kind`.
    let mut bad = base.clone();
    bad["invariants"]["points"][1]["locals"][0]["value"] =
        serde_json::json!({ "kind": "f32-interval", "interval": { "lo": 1, "hi": 1 } });
    assert!(
        !validator.is_valid(&bad),
        "unknown abstract-value kind must be rejected"
    );

    // 2. i32-interval missing its `interval` payload.
    let mut bad = base.clone();
    bad["invariants"]["points"][1]["locals"][0]["value"] =
        serde_json::json!({ "kind": "i32-interval" });
    assert!(
        !validator.is_valid(&bad),
        "i32-interval without interval must be rejected"
    );

    // 3. unexpected additional property on a closed object.
    let mut bad = base.clone();
    bad["invariants"]["bogus"] = serde_json::json!(1);
    assert!(
        !validator.is_valid(&bad),
        "additionalProperties on invariant-bundle must be rejected"
    );

    // 4. wrong `schema` URI const.
    let mut bad = base.clone();
    bad["invariants"]["schema"] = serde_json::json!("https://example.com/other");
    assert!(
        !validator.is_valid(&bad),
        "wrong schema URI const must be rejected"
    );

    // 5. malformed module-sha256 (not 64 lowercase hex).
    let mut bad = base.clone();
    bad["invariants"]["module-sha256"] = serde_json::json!("NOTAHEXDIGEST");
    assert!(
        !validator.is_valid(&bad),
        "bad module-sha256 pattern must be rejected"
    );

    // 6. invalid soundness enum value.
    let mut bad = base.clone();
    bad["call-graph"][0]["soundness"] = serde_json::json!("maybe");
    assert!(
        !validator.is_valid(&bad),
        "invalid soundness enum must be rejected"
    );

    // 7. dropping a required top-level field.
    base.as_object_mut().unwrap().remove("call-graph");
    assert!(
        !validator.is_valid(&base),
        "missing required call-graph must be rejected"
    );
}

/// FEAT-002: the optional `provenance` field is backward-compatible and
/// tightly typed. A document with no provenance (the v0.6 shape) still
/// validates; a well-formed provenance map validates; a malformed one is
/// rejected.
#[test]
#[allow(clippy::no_effect)]
fn provenance_is_optional_and_tight() {
    let validator = compile();

    // With provenance (the representative value carries it).
    let with_prov = serde_json::to_value(representative_result()).expect("serialize");
    assert!(
        with_prov.is_object() && with_prov.get("provenance").is_some(),
        "representative value must carry provenance"
    );
    assert!(
        validator.is_valid(&with_prov),
        "a value WITH provenance must validate"
    );

    // Without provenance — a v0.6-shaped document. Backward compat: the
    // optional field's absence must still validate.
    let mut without_prov = with_prov.clone();
    without_prov.as_object_mut().unwrap().remove("provenance");
    assert!(
        validator.is_valid(&without_prov),
        "a v0.6 document with no provenance must still validate (backward compat)"
    );

    // Malformed: an origin missing a required field.
    let mut bad = with_prov.clone();
    bad["provenance"]["origins"][0] =
        serde_json::json!({ "fused-func-index": 0, "component-id": 0 });
    assert!(
        !validator.is_valid(&bad),
        "component-origin missing orig-func-index must be rejected"
    );

    // Malformed: an unexpected property on the closed origin object.
    let mut bad = with_prov.clone();
    bad["provenance"]["origins"][0]["bogus"] = serde_json::json!(1);
    assert!(
        !validator.is_valid(&bad),
        "additionalProperties on component-origin must be rejected"
    );

    // Malformed: an unexpected property on the closed provenance object.
    let mut bad = with_prov;
    bad["provenance"]["extra"] = serde_json::json!(true);
    assert!(
        !validator.is_valid(&bad),
        "additionalProperties on component-provenance must be rejected"
    );
}
