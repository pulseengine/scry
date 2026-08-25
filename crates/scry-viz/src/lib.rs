//! # scry-viz — static-HTML visualization of a scry `AnalysisResult`
//!
//! scry already follows a "static-site evidence" pattern for MC/DC truth
//! tables (witness-viz, a CI artifact you can open from `file://`). `scry-viz`
//! is the analogue for the analyzer's *own* output: it turns an
//! [`scry_analyze_core::AnalysisResult`] into a single self-contained HTML page
//! a human can audit — no server, no JavaScript, no external assets.
//!
//! The page renders, in order:
//!   * a header with the module SHA-256, schema, and headline counts;
//!   * a **functions** table (reachable-from-exports? · recursive? · shadow-stack
//!     frame · worst-case stack), merging [`StackUsage`], [`FunctionSummary`],
//!     and `reachable_from_exports`;
//!   * the **call graph** (caller · pc · direct/indirect · resolved targets ·
//!     soundness tag);
//!   * **diagnostics** (severity · func:pc · message);
//!   * the **per-program-point invariants** — for each visited `(func, pc)`,
//!     the abstract `locals` AND the abstract `operand_stack` (FEAT-023), in
//!     stack order bottom → top.
//!
//! ## Soundness posture
//!
//! `scry-viz` is a faithful *rendering*: it re-derives nothing and asserts
//! nothing beyond what the `AnalysisResult` already states. Every value shown
//! is a verbatim projection of an analyzer field. An empty operand-stack at a
//! program point is shown as the literal "(empty)" — it is the analyzer's
//! honest "no operand-stack info here" (e.g. a write-set-havoc point), not a
//! claim that the concrete stack is empty.

use core::fmt::Write as _;

use scry_analyze_core::{
    AbstractValue, AdvisoryClass, AnalysisResult, Diagnostic, DiagnosticSeverity, FunctionMeta,
    FunctionStack, GapKind, HandleFindingKind, Interval, PentagonBound, Region, SecurityLabel,
    SoundnessTag, StackBound, TaintFindingKind, TrapKind, TrapVerdict,
};

/// The hero / page title — a precise, scoped one-liner (not "verification
/// dashboard"). Used in both the `<title>` and the `<h1>`.
const HERO_TITLE: &str = "scry — a sound static analyzer for WebAssembly";

/// Program-points cap: the number of per-function points rendered inline in a
/// detailed table. Above this, a function shows its first `POINTS_PER_FN_CAP`
/// points and a "… showing N of M" note.
const POINTS_PER_FN_CAP: usize = 20;

/// Row cap for the flat list/table sections (Diagnostics, Call graph, Trap
/// checks, Functions, gaps, …). scry-on-scry produces thousands of rows in each
/// (Info diagnostics per bounds-check, 1349 call edges, thousands of trap
/// checks); un-capped they are megabytes of noise. Each section shows the first
/// `SECTION_ROW_CAP` rows and a "showing N of M" note; the actionable subset is
/// in the guidance.json feed.
const SECTION_ROW_CAP: usize = 100;

/// Cap on the number of FUNCTIONS rendered with a detailed per-point table.
/// scry-on-scry has ~800 functions, so a per-function cap alone still yields a
/// multi-MB dump (800 × 20 rows). All four persona reviews found the raw
/// per-point dump is noise for readers, so every function appears in a cheap
/// one-row summary and only the first `FUNCS_WITH_DETAIL_CAP` get a detailed
/// table; the full per-point invariants are scry's library `AnalysisResult`.
const FUNCS_WITH_DETAIL_CAP: usize = 12;

/// Guidance cap: for every advisory class EXCEPT `DefiniteFault` (always shown
/// in full — proven bugs), render at most this many rows, then a "… and N more"
/// line. Faults are never elided.
const ADVISORY_PER_CLASS_CAP: usize = 10;

/// FEAT-027: metadata for one function index, if scry resolved any.
fn fn_meta(r: &AnalysisResult, idx: u32) -> Option<&FunctionMeta> {
    r.function_meta.iter().find(|m| m.func_index == idx)
}

/// FEAT-029: a name resolved for display — the demangled (human-readable) form,
/// the exact raw symbol, and a best-guess source language. Demangling is
/// deterministic *decoding*; the language is only a guess, so it's set ONLY
/// when a demangler actually accepted the symbol, and `raw` is always kept so
/// the hover can show the exact source string (nothing is hidden).
struct Shown {
    display: String,
    raw: String,
    lang: Option<&'static str>,
}

/// Demangle a wasm-`name`-section symbol: Rust legacy (`_ZN…E`) and v0 (`_R…`)
/// via rustc-demangle (hash stripped with the `{:#}` formatter), Itanium C++
/// (`_Z…`) via cpp_demangle. A plain/C name matches neither and is returned
/// unchanged with no language.
fn demangle(raw: &str) -> Shown {
    if let Ok(d) = rustc_demangle::try_demangle(raw) {
        return Shown {
            display: format!("{d:#}"),
            raw: raw.to_string(),
            lang: Some("rust"),
        };
    }
    if let Ok(sym) = cpp_demangle::Symbol::new(raw)
        && let Ok(d) = sym.demangle()
    {
        return Shown {
            display: d,
            raw: raw.to_string(),
            lang: Some("c++"),
        };
    }
    Shown {
        display: raw.to_string(),
        raw: raw.to_string(),
        lang: None,
    }
}

/// FEAT-029: render a name for a table cell / heading — the demangled text in a
/// CSS-ellipsized span whose `title` (hover) carries the full demangled name
/// and, when it differs, the raw mangled symbol. Everything HTML-escaped, so a
/// long name is shortened in place with the complete form one hover away.
fn name_span(sh: &Shown) -> String {
    let title = if sh.display != sh.raw {
        format!("{}\n[symbol] {}", sh.display, sh.raw)
    } else {
        sh.display.clone()
    };
    format!(
        "<span class=\"nm\" title=\"{}\">{}</span>",
        esc(&title),
        esc(&sh.display),
    )
}

/// A small language tag (`rust` / `c++`) shown only when demangling identified
/// the source language. Empty otherwise — we do not guess a language for an
/// un-mangled (e.g. C / hand-written) name.
fn lang_badge(sh: &Shown) -> String {
    match sh.lang {
        Some(l) => format!("<span class=\"badge lang\">{l}</span> "),
        None => String::new(),
    }
}

/// A function reference as a link to its row in the Functions table, showing
/// the demangled name when there is one: `42 compute` (or just `42`).
fn fn_link(r: &AnalysisResult, idx: u32) -> String {
    match fn_meta(r, idx).and_then(|m| m.name.as_deref()) {
        Some(n) => format!(
            "<a href=\"#fn-{idx}\">{idx} {}</a>",
            name_span(&demangle(n))
        ),
        None => format!("<a href=\"#fn-{idx}\">{idx}</a>"),
    }
}

/// Kind badges for a function: `import`, `export "run"` (one per export), or a
/// muted `defined` when neither.
fn kind_badges(m: Option<&FunctionMeta>) -> String {
    let mut out = String::new();
    if let Some(m) = m {
        if m.imported {
            out.push_str("<span class=\"badge import\">import</span> ");
        }
        for ex in &m.exports {
            let _ = write!(
                out,
                "<span class=\"badge export\">export \"{}\"</span> ",
                esc(ex)
            );
        }
    }
    if out.is_empty() {
        out.push_str("<span class=\"muted\">defined</span>");
    }
    out
}

/// Render a complete, self-contained HTML document for `result`.
///
/// `title` is shown in the page `<title>` and `<h1>` — typically the analyzed
/// module's name. The returned `String` is the entire document (UTF-8); write
/// it to a `.html` file and open it directly.
pub fn render_html(result: &AnalysisResult, title: &str) -> String {
    let mut s = String::with_capacity(8 * 1024);
    let _ = write!(s, "{}", DOCTYPE_AND_HEAD_OPEN);
    // The scoped hero title (`HERO_TITLE`), then the per-page title.
    let _ = write!(s, "<title>{} — {}</title>", esc(HERO_TITLE), esc(title));
    let _ = write!(s, "{}", STYLE);
    s.push_str("</head><body>");

    let _ = write!(s, "<h1>{} — {}</h1>", esc(HERO_TITLE), esc(title));
    render_header(&mut s, result);
    render_scope(&mut s, result);
    render_advisories(&mut s, result);
    render_functions(&mut s, result);
    render_call_graph(&mut s, result);
    render_diagnostics(&mut s, &result.diagnostics);
    render_gaps(&mut s, result);
    render_trap_checks(&mut s, result);
    render_handle_findings(&mut s, result);
    render_float_facts(&mut s, result);
    render_pentagon_facts(&mut s, result);
    render_taint(&mut s, result);
    render_provenance(&mut s, result);
    render_points(&mut s, result);

    s.push_str(
        "<footer>Rendered by scry-viz · a faithful projection of the \
        analyzer output (nothing re-derived). MIT OR Apache-2.0.</footer>",
    );
    s.push_str("</body></html>");
    s
}

/// One linked view on the landing page produced by [`render_index`].
pub struct IndexEntry {
    /// Relative href into the deployed site (e.g. `self-analysis.html`).
    pub href: String,
    /// Card title.
    pub title: String,
    /// One-line description of what the view shows.
    pub description: String,
}

/// Render a self-contained landing page that links a set of dashboard views —
/// the analogue of `witness-viz pages-index`. Used to tie the scry-viz
/// self-analysis and the MC/DC truth-table dashboard together at the root of
/// the GitHub Pages site (FEAT-026). Like every scry-viz page it asserts
/// nothing beyond the links it is given; `site_title` and each entry are
/// HTML-escaped.
pub fn render_index(site_title: &str, entries: &[IndexEntry]) -> String {
    let mut s = String::with_capacity(2 * 1024);
    let _ = write!(s, "{}", DOCTYPE_AND_HEAD_OPEN);
    let _ = write!(s, "<title>{}</title>", esc(site_title));
    let _ = write!(s, "{}", STYLE);
    s.push_str("</head><body>");
    let _ = write!(s, "<h1>{}</h1>", esc(site_title));
    s.push_str(
        "<p class=\"muted\">scry is a <strong>sound</strong> (over-approximating) \
         static analyzer for WebAssembly core modules: it proves properties that \
         hold on <em>every</em> run. It catches out-of-bounds / divide-by-zero / \
         overflow traps (proven-safe vs potential), use-after-drop on component \
         handles, and bounds on the shadow stack. A ⊤ (\"top\") or POTENTIAL-TRAP \
         verdict means <em>unknown</em> — never \"safe\". These pages are a \
         faithful projection of the analyzer's own output; nothing is re-derived.</p>",
    );
    if entries.is_empty() {
        s.push_str("<p class=\"empty\">No views available.</p>");
    } else {
        s.push_str("<ul class=\"cards\">");
        for e in entries {
            let _ = write!(
                s,
                "<li><a href=\"{}\"><strong>{}</strong></a><div class=\"muted\">{}</div></li>",
                esc(&e.href),
                esc(&e.title),
                esc(&e.description),
            );
        }
        s.push_str("</ul>");
    }
    s.push_str(
        "<footer>Generated by scry-viz · MIT OR Apache-2.0 · \
         <a href=\"https://github.com/pulseengine/scry\">pulseengine/scry</a></footer>",
    );
    s.push_str("</body></html>");
    s
}

fn render_header(s: &mut String, r: &AnalysisResult) {
    let points = r.invariants.points.len();
    let reachable = r.reachable_from_exports.len();
    let recursive = r.function_summaries.iter().filter(|f| f.recursive).count();
    s.push_str("<section class=\"summary\"><h2>Summary</h2><dl>");
    kv(s, "module sha256", &r.invariants.module_sha256);
    kv(s, "schema", &r.invariants.schema);
    kv(
        s,
        "worst-case shadow stack",
        &stack_bound(&r.stack_usage.max_stack_bytes),
    );
    kv(
        s,
        "stack-pointer global",
        &match r.stack_usage.sp_global {
            Some(g) => format!("global {g}"),
            None => "none (no shadow stack)".to_string(),
        },
    );
    kv(
        s,
        "functions (summarized)",
        &r.function_summaries.len().to_string(),
    );
    kv(s, "reachable from exports", &reachable.to_string());
    kv(s, "recursive functions", &recursive.to_string());
    kv(s, "call-graph edges", &r.call_graph.len().to_string());
    kv(s, "diagnostics", &r.diagnostics.len().to_string());
    kv(s, "analysis gaps", &r.gaps.len().to_string());
    kv(s, "relational guards", &r.pentagon_facts.len().to_string());
    kv(s, "trap checks", &r.trap_checks.len().to_string());
    kv(s, "handle faults", &r.handle_findings.len().to_string());
    kv(s, "advisories", &r.advisories.len().to_string());
    kv(s, "float facts", &r.float_facts.len().to_string());
    kv(s, "program points", &points.to_string());
    // FEAT-034: scry's own verified fusion premises (independent of meld).
    let vp = &r.verified_premises;
    kv(
        s,
        "verified premises",
        &format!(
            "bounded-memory: {} · closed-world: {}",
            if vp.bounded_memory { "yes" } else { "no" },
            if vp.closed_world { "yes" } else { "no" },
        ),
    );
    s.push_str("</dl></section>");
}

/// A scope & limitations block. The copy is intentionally a placeholder — the
/// maintainer writes the precise soundness claims (what scry proves, its
/// abstract-domain limits, what a gap/advisory does and does NOT assert). We
/// only lay out the section so the page has a home for it.
fn render_scope(s: &mut String, _r: &AnalysisResult) {
    s.push_str(
        "<section id=\"scope\"><h2>Scope &amp; limitations</h2>\
         <p>scry is a <strong>sound</strong> abstract interpreter: every reported \
         invariant, bound, and PROVEN-SAFE verdict holds on all runs — it never \
         misses a real behaviour. The price is over-approximation: \
         <strong>⊤ (\"top\") and POTENTIAL-TRAP mean \"scry could not decide\", never \
         \"safe\"</strong>. An analysis <em>gap</em> records where a domain gave up; \
         it asserts nothing about the code, only that scry was imprecise there.</p>\
         <h3>Evidence kinds (strongest first)</h3>\
         <ul>\
         <li><strong>Mechanized (Rocq, admit-free, CI-gated):</strong> the \
         abstract-domain lattices and core transfers — interval soundness over ℤ; \
         <code>i32.add</code> vs the OFFICIAL two's-complement wrapping semantics \
         including the wrap case (<code>WrapAdd.v</code>); region, call-graph, \
         reachability, octagon, pentagon, float-lattice, known-bits, handle-state, \
         linear-memory segmentation, and convex-polyhedra <em>lattice</em> proofs.</li>\
         <li><strong>γ-sweep-validated (tested, NOT mechanized):</strong> the harder \
         transfer algorithms — float round-to-nearest arithmetic, known-bits value \
         transfers at w=32/64 (tracked: issue #105), and the polyhedra \
         Fourier–Motzkin entailment + hull over-approximation. Exhaustively checked \
         against a concrete oracle on a value grid, but not machine-proven.</li>\
         <li><strong>Runnable / attested:</strong> the shadow-stack bound is \
         cross-checked against a real wasmtime run; releases are cosign-signed.</li>\
         </ul>\
         <h3>What scry does NOT (yet) prove / where it is conservative</h3>\
         <ul>\
         <li>It models the official Wasm semantics <em>directly</em>; it does not \
         yet <em>import</em> the canonical WasmCert-Coq mechanization, and the \
         official-semantics proof so far covers <code>i32.add</code>, not every \
         transfer.</li>\
         <li>Linear-memory content is tracked only for singleton in-bounds i32 \
         accesses; a loop-range fill is soundly forgotten (⊤), and any call forgets \
         memory content.</li>\
         <li>scry ships a DO-330 / ISO 26262 evidence <em>dossier</em> but is not \
         itself a qualified tool — this dashboard makes no TQL / TCL claim.</li>\
         </ul></section>",
    );
}

fn render_functions(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Functions</h2>");
    if r.function_summaries.is_empty()
        && r.stack_usage.functions.is_empty()
        && r.function_meta.is_empty()
    {
        s.push_str("<p class=\"empty\">No functions.</p></section>");
        return;
    }
    s.push_str(
        "<table><thead><tr><th>func</th><th>name</th><th>kind</th><th>reachable</th>\
         <th>recursive</th><th>params</th><th>frame</th><th>max stack</th><th>points</th>\
         </tr></thead><tbody>",
    );
    // The `reachable` column reads `reachable_from_exports` via binary_search,
    // which is only correct if that vector is sorted ascending — which scry's
    // `compute_reachable_from_exports` guarantees (sort_unstable + dedup, per
    // its doc + analyzer test). Defend our own correctness against an upstream
    // regression: a future change that returned it unsorted would silently
    // mis-render reachability, so we self-check in debug/test builds.
    debug_assert!(
        r.reachable_from_exports.is_sorted(),
        "reachable_from_exports must be sorted ascending for binary_search"
    );
    // Union of every function index we know something about (FEAT-027 metadata
    // covers imports too, which have no summary/stack entry), ascending.
    let mut indices: Vec<u32> = r
        .function_summaries
        .iter()
        .map(|f| f.func_index)
        .chain(r.stack_usage.functions.iter().map(|f| f.func_index))
        .chain(r.function_meta.iter().map(|m| m.func_index))
        .collect();
    indices.sort_unstable();
    indices.dedup();
    let n_funcs = indices.len();
    for idx in indices.into_iter().take(SECTION_ROW_CAP) {
        let meta = fn_meta(r, idx);
        let summary = r.function_summaries.iter().find(|f| f.func_index == idx);
        let stack: Option<&FunctionStack> =
            r.stack_usage.functions.iter().find(|f| f.func_index == idx);
        let reachable = r.reachable_from_exports.binary_search(&idx).is_ok();
        let recursive = summary.map(|f| f.recursive).unwrap_or(false);
        let params = summary
            .map(|f| f.param_count.to_string())
            .unwrap_or_else(|| "?".into());
        let frame = stack
            .map(|f| stack_bound(&f.frame))
            .unwrap_or_else(|| "?".into());
        let maxs = stack
            .map(|f| stack_bound(&f.max_stack))
            .unwrap_or_else(|| "?".into());
        // FEAT-029: demangle for display; the raw symbol stays on hover, and a
        // language tag rides in the kind column when a demangler identified it.
        let shown = meta.and_then(|m| m.name.as_deref()).map(demangle);
        let name = match &shown {
            Some(sh) => name_span(sh),
            None => "<span class=\"muted\">—</span>".to_string(),
        };
        let lang = shown.as_ref().map(lang_badge).unwrap_or_default();
        let n_points = r
            .invariants
            .points
            .iter()
            .filter(|p| p.func_index == idx)
            .count();
        let points_cell = if n_points > 0 {
            format!("<a href=\"#pts-{idx}\">{n_points}</a>")
        } else {
            "<span class=\"muted\">0</span>".to_string()
        };
        let _ = write!(
            s,
            "<tr id=\"fn-{idx}\"><td>{idx}</td><td>{name}</td><td>{}{}</td><td>{}</td>\
             <td>{}</td><td>{params}</td><td>{frame}</td><td>{maxs}</td><td>{points_cell}</td></tr>",
            lang,
            kind_badges(meta),
            yesno(reachable),
            yesno(recursive),
        );
    }
    s.push_str("</tbody></table>");
    cap_note(s, n_funcs, "functions");
    s.push_str("</section>");
}

fn render_call_graph(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Call graph</h2>");
    if r.call_graph.is_empty() {
        s.push_str("<p class=\"empty\">No call edges.</p></section>");
        return;
    }
    s.push_str(
        "<table><thead><tr><th>caller</th><th>pc</th><th>kind</th>\
         <th>resolved targets</th><th>soundness</th></tr></thead><tbody>",
    );
    for e in r.call_graph.iter().take(SECTION_ROW_CAP) {
        // FEAT-027: resolve caller + target indices to named links so an edge
        // reads `1 $compute → 2 $helper`, and each end jumps to its row.
        let targets = if e.resolved_targets.is_empty() {
            "<span class=\"muted\">(none)</span>".to_string()
        } else {
            e.resolved_targets
                .iter()
                .map(|t| fn_link(r, *t))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let sound = match e.soundness {
            SoundnessTag::Sound => "<span class=\"ok\">sound</span>",
            SoundnessTag::UnsoundFallback => "<span class=\"warn\">unsound-fallback</span>",
        };
        let _ = write!(
            s,
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{targets}</td><td>{sound}</td></tr>",
            fn_link(r, e.caller_func),
            e.pc,
            if e.indirect { "call_indirect" } else { "call" },
        );
    }
    s.push_str("</tbody></table>");
    cap_note(s, r.call_graph.len(), "call edges");
    // FEAT-028: a call-graph DIAGRAM. Inline SVG for graphs small enough to lay
    // out cleanly; the Mermaid source otherwise. Skipped entirely for very large
    // graphs (a Mermaid source of thousands of edges is itself megabytes of noise
    // — the edge table above + guidance.json feed carry the data).
    if r.call_graph.len() <= SECTION_ROW_CAP {
        render_callgraph_diagram(s, r);
    }
    s.push_str("</section>");
}

/// Largest node count we lay out as inline SVG. Above this the SVG would be an
/// unreadable tangle, so we emit only the Mermaid source (which an external
/// renderer can lay out).
const DIAGRAM_SVG_NODE_CAP: usize = 48;

/// FEAT-028: render the call graph as a diagram. Two faithful projections of
/// the same edges (nothing inferred): an inline SVG (drawn at build time, no
/// JS, works from `file://`) when the graph is small, plus the Mermaid `graph`
/// source in a `<details>` for export to any Mermaid renderer (GitHub,
/// mermaid.live, …). Direct calls are solid, `call_indirect` dashed, and an
/// unsound-fallback edge is red — matching the table's soundness column.
fn render_callgraph_diagram(s: &mut String, r: &AnalysisResult) {
    // Collect the directed edges (caller → each resolved target) and the node
    // set. An indirect site with no resolved target contributes no edge.
    let mut edges: Vec<DiagramEdge> = Vec::new();
    let mut nodes: Vec<u32> = Vec::new();
    let push_node = |nodes: &mut Vec<u32>, n: u32| {
        if !nodes.contains(&n) {
            nodes.push(n);
        }
    };
    for e in &r.call_graph {
        for &t in &e.resolved_targets {
            push_node(&mut nodes, e.caller_func);
            push_node(&mut nodes, t);
            edges.push(DiagramEdge {
                from: e.caller_func,
                to: t,
                indirect: e.indirect,
                unsound: matches!(e.soundness, SoundnessTag::UnsoundFallback),
            });
        }
    }
    nodes.sort_unstable();
    if nodes.is_empty() {
        s.push_str(
            "<p class=\"muted\">No resolved call edges to diagram (any indirect \
             sites had no resolved targets).</p>",
        );
        return;
    }

    s.push_str("<h3 class=\"fn-points\">Call-graph diagram</h3>");
    if nodes.len() <= DIAGRAM_SVG_NODE_CAP {
        render_callgraph_svg(s, r, &nodes, &edges);
    } else {
        let _ = write!(
            s,
            "<p class=\"muted\">{} functions — too large to lay out inline; \
             use the Mermaid source below.</p>",
            nodes.len(),
        );
    }
    // Mermaid source (always) — copy into any Mermaid renderer.
    s.push_str(
        "<details><summary>Mermaid source</summary>\
         <pre class=\"mermaid-src\">",
    );
    s.push_str(&esc(&mermaid_source(r, &nodes, &edges)));
    s.push_str("</pre></details>");
}

struct DiagramEdge {
    from: u32,
    to: u32,
    indirect: bool,
    unsound: bool,
}

/// Mermaid `graph LR` text for the call graph. Node ids are `n{idx}`; labels
/// are `idx name`. Direct edges `-->`, indirect `-.->`. (Mermaid does its own
/// layout; this is the export/large-graph path.)
fn mermaid_source(r: &AnalysisResult, nodes: &[u32], edges: &[DiagramEdge]) -> String {
    let mut m = String::from("graph LR\n");
    for &n in nodes {
        // Mermaid labels go in quotes; use the demangled name and sanitize the
        // few chars that break the `["…"]` label — drop quotes/newlines and map
        // square brackets (common in demangled types like `[u8; 4]`, which
        // would prematurely close the label) to parens. The whole block is
        // additionally HTML-escaped before it enters the <pre>.
        let label = match fn_meta(r, n).and_then(|x| x.name.as_deref()) {
            Some(name) => {
                let d = demangle(name).display.replace(['"', '\n'], "");
                format!("{n} {}", d.replace('[', "(").replace(']', ")"))
            }
            None => format!("{n}"),
        };
        let _ = writeln!(m, "  n{n}[\"{label}\"]", label = label);
    }
    for e in edges {
        let arrow = if e.indirect { "-.->" } else { "-->" };
        let _ = writeln!(m, "  n{} {arrow} n{}", e.from, e.to);
    }
    m
}

/// A layered inline-SVG drawing of the call graph: longest-path layering
/// (cycles bounded), columns left→right, nodes stacked within a column, edges
/// as bezier curves. Self-contained, no JS.
fn render_callgraph_svg(s: &mut String, r: &AnalysisResult, nodes: &[u32], edges: &[DiagramEdge]) {
    use std::collections::BTreeMap;

    // ── Longest-path layering. layer[n] = longest directed path (in the node
    // set) ending at n; cycles are naturally bounded by the iteration cap, so
    // a back-edge simply doesn't push its target further right. ──
    let mut layer: BTreeMap<u32, u32> = nodes.iter().map(|&n| (n, 0u32)).collect();
    for _ in 0..nodes.len() {
        let mut changed = false;
        for e in edges {
            if e.from == e.to {
                continue; // self-loop: no layer effect
            }
            let want = layer[&e.from] + 1;
            if let Some(l) = layer.get_mut(&e.to)
                && *l < want
            {
                *l = want;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Group nodes by layer (column); order within a column by func index.
    let mut columns: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for &n in nodes {
        columns.entry(layer[&n]).or_default().push(n);
    }

    // Geometry.
    const COL_W: u32 = 200;
    const ROW_H: u32 = 44;
    const BOX_W: u32 = 160;
    const BOX_H: u32 = 26;
    const MARGIN: u32 = 16;
    let n_cols = columns.keys().max().copied().unwrap_or(0) + 1;
    let max_rows = columns.values().map(|c| c.len()).max().unwrap_or(1) as u32;
    let width = MARGIN * 2 + n_cols * COL_W;
    let height = MARGIN * 2 + max_rows.max(1) * ROW_H;

    // Node centre coordinates.
    let mut pos: BTreeMap<u32, (u32, u32)> = BTreeMap::new();
    for (&col, members) in &columns {
        for (row, &n) in members.iter().enumerate() {
            let x = MARGIN + col * COL_W;
            let y = MARGIN + row as u32 * ROW_H;
            pos.insert(n, (x, y));
        }
    }

    let _ = write!(
        s,
        "<svg class=\"cg\" viewBox=\"0 0 {width} {height}\" width=\"{width}\" \
         height=\"{height}\" role=\"img\" aria-label=\"call graph\">",
    );
    // Edges first (under nodes). Bezier from right-mid of source to left-mid of
    // target; a back/level edge (target not strictly to the right) still draws.
    for e in edges {
        let (Some(&(fx, fy)), Some(&(tx, ty))) = (pos.get(&e.from), pos.get(&e.to)) else {
            continue;
        };
        let (x1, y1) = (fx + BOX_W, fy + BOX_H / 2);
        let (x2, y2) = (tx, ty + BOX_H / 2);
        let mx = (x1 + x2) / 2;
        let mut cls = String::from("e");
        if e.indirect {
            cls.push_str(" ind");
        }
        if e.unsound {
            cls.push_str(" uns");
        }
        let _ = write!(
            s,
            "<path class=\"{cls}\" d=\"M{x1},{y1} C{mx},{y1} {mx},{y2} {x2},{y2}\"/>",
        );
    }
    // Nodes.
    for &n in nodes {
        let (x, y) = pos[&n];
        let meta = fn_meta(r, n);
        let mut cls = String::from("nd");
        if meta.map(|m| m.imported).unwrap_or(false) {
            cls.push_str(" imp");
        }
        if meta.map(|m| !m.exports.is_empty()).unwrap_or(false) {
            cls.push_str(" exp");
        }
        // FEAT-029: box shows the (truncated) demangled name; the SVG <title>
        // hover carries the full demangled name plus the raw symbol.
        let (label, title) = match meta.and_then(|m| m.name.as_deref()) {
            Some(name) => {
                let sh = demangle(name);
                let title = if sh.display != sh.raw {
                    format!("{n} {}\n[symbol] {}", sh.display, sh.raw)
                } else {
                    format!("{n} {}", sh.display)
                };
                (format!("{n} {}", sh.display), title)
            }
            None => (format!("{n}"), format!("{n}")),
        };
        let shown = truncate_label(&label, 20);
        let _ = write!(
            s,
            "<g class=\"{cls}\"><title>{}</title>\
             <rect x=\"{x}\" y=\"{y}\" width=\"{BOX_W}\" height=\"{BOX_H}\" rx=\"4\"/>\
             <text x=\"{tx}\" y=\"{ty}\">{}</text></g>",
            esc(&title),
            esc(&shown),
            tx = x + 8,
            ty = y + BOX_H / 2 + 4,
        );
    }
    s.push_str("</svg>");
}

/// Truncate a label to `max` chars with an ellipsis (the full name stays in the
/// SVG `<title>` tooltip).
fn truncate_label(label: &str, max: usize) -> String {
    if label.chars().count() <= max {
        label.to_string()
    } else {
        let mut out: String = label.chars().take(max.saturating_sub(1)).collect();
        out.push('…');
        out
    }
}

/// FEAT-040: analysis gaps — the explicit "scry was conservative here" sites
/// (an unsupported op that degraded a function to ⊤). Rendered as a structured
/// table so an assessor (the qualification scope/limitation statement) or an AI
/// agent reads the gaps as DATA, not as the silence of an absent fact.
fn render_gaps(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Analysis gaps</h2>");
    if r.gaps.is_empty() {
        s.push_str("<p class=\"empty\">No gaps — every analyzed function stayed within scry's modelled set.</p></section>");
        return;
    }
    let _ = write!(
        s,
        "<p>{} site(s) where scry degraded a function to \u{22a4} (gave up).</p><ul class=\"diags\">",
        r.gaps.len(),
    );
    for g in r.gaps.iter().take(SECTION_ROW_CAP) {
        let kind = match g.kind {
            GapKind::UnsupportedOp => "unsupported-op",
            GapKind::UnmodeledBranch => "unmodeled-branch",
            GapKind::UnmodeledMemoryAddress => "unmodeled-memory-address",
            GapKind::UnmodeledControlFlow => "unmodeled-control-flow",
        };
        let _ = write!(
            s,
            "<li class=\"err\"><span class=\"sev\">{kind}</span> \
             <code>fn{}:{}</code> {}</li>",
            g.func_index,
            g.pc,
            esc(&g.op),
        );
    }
    s.push_str("</ul>");
    cap_note(s, r.gaps.len(), "gaps");
    s.push_str("</section>");
}

/// FEAT-045: division/remainder trap classifications — scry's first runtime-
/// error verdict. PROVEN-SAFE divisions are shown alongside POTENTIAL-TRAPs so
/// an assessor sees the proof obligations discharged, not just the warnings.
fn render_trap_checks(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Trap checks (div/rem + memory)</h2>");
    if r.trap_checks.is_empty() {
        s.push_str(
            "<p class=\"empty\">No trapping operators (div/rem/load/store) analyzed.</p></section>",
        );
        return;
    }
    let traps = r
        .trap_checks
        .iter()
        .filter(|t| t.verdict == TrapVerdict::PotentialTrap)
        .count();
    let _ = write!(
        s,
        "<p>{} check(s); {} POTENTIAL-TRAP, {} PROVEN-SAFE.</p><ul class=\"diags\">",
        r.trap_checks.len(),
        traps,
        r.trap_checks.len() - traps,
    );
    // POTENTIAL-TRAPs first (the actionable proof obligations), then
    // PROVEN-SAFE, capped — so the cap never hides a potential trap behind
    // thousands of proven-safe rows. The tally above is exact; the full set is
    // in the guidance.json feed.
    let ordered = r
        .trap_checks
        .iter()
        .filter(|t| t.verdict == TrapVerdict::PotentialTrap)
        .chain(
            r.trap_checks
                .iter()
                .filter(|t| t.verdict == TrapVerdict::ProvenSafe),
        );
    for t in ordered.take(SECTION_ROW_CAP) {
        let (cls, verdict) = match t.verdict {
            TrapVerdict::ProvenSafe => ("info", "PROVEN-SAFE"),
            TrapVerdict::PotentialTrap => ("err", "POTENTIAL-TRAP"),
        };
        let kind = match t.kind {
            TrapKind::DivByZero => "div-by-zero",
            TrapKind::SignedOverflow => "signed-overflow",
            TrapKind::OutOfBounds => "out-of-bounds",
        };
        let _ = write!(
            s,
            "<li class=\"{cls}\"><span class=\"sev\">{verdict}</span> \
             <code>fn{}:{}</code> {} ({kind})</li>",
            t.func_index,
            t.pc,
            esc(&t.op),
        );
    }
    s.push_str("</ul>");
    cap_note(s, r.trap_checks.len(), "trap checks");
    s.push_str("</section>");
}

/// FEAT-059/060: the remediation Guidance panel — the actionable "what to do"
/// synthesis, prioritised by class (faults first), with a one-line summary. The
/// headline view for a human; the same records feed the agent JSON schema.
fn render_advisories(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Guidance — how to improve this code</h2>");
    if r.advisories.is_empty() {
        s.push_str("<p class=\"empty\">No advisories — no faults, unproven obligations, precision gaps, or leverageable facts surfaced.</p></section>");
        return;
    }
    let count = |c: AdvisoryClass| r.advisories.iter().filter(|a| a.class == c).count();
    let _ = write!(
        s,
        "<p><b>{}</b> real fault(s) to fix · <b>{}</b> unproven obligation(s) to prove/guard · \
         <b>{}</b> analyzer precision gap(s) · <b>{}</b> leverageable fact(s).</p><ul class=\"diags\">",
        count(AdvisoryClass::DefiniteFault),
        count(AdvisoryClass::UnprovenObligation),
        count(AdvisoryClass::PrecisionGap),
        count(AdvisoryClass::LeverageableFact),
    );
    // The boilerplate problem: on a real module, thousands of identical
    // `UnprovenObligation` rows drown the handful of proven-fault items. So we
    // render every `DefiniteFault` (a proven bug — never elide), but cap every
    // OTHER class at `ADVISORY_PER_CLASS_CAP` rows and print a "… and N more"
    // line pointing at the JSON feed, which carries the full set.
    for class in [
        AdvisoryClass::DefiniteFault,
        AdvisoryClass::UnprovenObligation,
        AdvisoryClass::PrecisionGap,
        AdvisoryClass::LeverageableFact,
    ] {
        let cap = if class == AdvisoryClass::DefiniteFault {
            usize::MAX
        } else {
            ADVISORY_PER_CLASS_CAP
        };
        let total = r.advisories.iter().filter(|a| a.class == class).count();
        for a in r.advisories.iter().filter(|a| a.class == class).take(cap) {
            render_advisory_row(s, a);
        }
        if total > cap {
            let _ = write!(
                s,
                "<li class=\"muted\">… and {} more {} (see the JSON feed)</li>",
                total - cap,
                advisory_class_name(class),
            );
        }
    }
    s.push_str("</ul></section>");
}

/// A machine-stable class name used in the collapse note and the JSON feed.
fn advisory_class_name(c: AdvisoryClass) -> &'static str {
    match c {
        AdvisoryClass::DefiniteFault => "definite-fault",
        AdvisoryClass::UnprovenObligation => "unproven-obligation",
        AdvisoryClass::PrecisionGap => "precision-gap",
        AdvisoryClass::LeverageableFact => "leverageable-fact",
    }
}

/// Render one advisory as a `<li>` — the shared body of the (capped) HTML
/// Guidance list.
///
/// FEAT-072: the row carries `id="ob-<obligation_id>"` and a `¶` permalink, so
/// an obligation is CITABLE by URL. Until now the only handle a consumer could
/// quote was `fn{index}:{pc}` — which is precisely the key that shifts on the
/// next edit, so the dashboard was handing out references it knew would break.
/// The `(func_index, pc)` pair stays visible as a positional convenience.
fn render_advisory_row(s: &mut String, a: &scry_analyze_core::Advisory) {
    let (cls, label) = match a.class {
        AdvisoryClass::DefiniteFault => ("err", "FIX"),
        AdvisoryClass::UnprovenObligation => ("warn", "PROVE/GUARD"),
        AdvisoryClass::PrecisionGap => ("info", "PRECISION"),
        AdvisoryClass::LeverageableFact => ("info", "LEVERAGE"),
    };
    // An empty id means no identity could be derived (FEAT-064). Emit no anchor
    // rather than a dead `#ob-` fragment that would resolve to the wrong row.
    if a.obligation_id.is_empty() {
        let _ = write!(s, "<li class=\"{cls}\">");
    } else {
        let _ = write!(
            s,
            "<li id=\"ob-{0}\" class=\"{cls}\"><a class=\"anchor\" href=\"#ob-{0}\" \
             title=\"content-addressed obligation id — stable while this function\'s \
             name and structure are (see scry#123)\">¶</a>",
            esc(&a.obligation_id),
        );
        // FEAT-076 (scry#123): a build-local identity must be visibly marked —
        // the id above is unique within THIS build only, so citing it across
        // builds is meaningless and a consumer must be able to tell without
        // parsing the id.
        if a.id_build_local {
            let _ = write!(
                s,
                "<span class=\"badge\" title=\"this function's stripped name is \
                 shared by another function (dependency generics), so the raw \
                 disambiguated name is hashed — the id is unique within this \
                 build only and NOT comparable across builds (scry#123)\">\
                 build-local id</span> "
            );
        }
    }
    let _ = write!(
        s,
        "<span class=\"sev\">{label}</span> \
         <code>fn{}:{} {}</code> — {}<br><em>Action:</em> {}<br><em>Verify:</em> {}",
        a.func_index,
        a.pc,
        esc(&a.code),
        esc(&a.detail),
        esc(&a.suggested_action),
        esc(&a.verification),
    );
    if let Some(cx) = &a.counterexample {
        let _ = write!(
            s,
            "<br><em>Counterexample (candidate):</em> {}",
            esc(&cx.trigger)
        );
        if !cx.witness.is_empty() {
            s.push_str(" [");
            for (i, w) in cx.witness.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                let _ = write!(s, "{}={}", esc(&w.operand), w.value);
            }
            s.push(']');
        }
    }
    s.push_str("</li>");
}

/// FEAT-049: Component-Model handle-lifetime faults — use-after-drop /
/// double-drop on affine resource handles (the uncontested green field).
fn render_handle_findings(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Handle-state faults (component model)</h2>");
    if r.handle_findings.is_empty() {
        s.push_str("<p class=\"empty\">No use-after-drop / double-drop faults.</p></section>");
        return;
    }
    let _ = write!(
        s,
        "<p>{} handle-lifetime fault(s).</p><ul class=\"diags\">",
        r.handle_findings.len(),
    );
    for h in r.handle_findings.iter().take(SECTION_ROW_CAP) {
        let kind = match h.kind {
            HandleFindingKind::UseAfterDrop => "use-after-drop",
            HandleFindingKind::DoubleDrop => "double-drop",
        };
        let _ = write!(
            s,
            "<li class=\"err\"><span class=\"sev\">{kind}</span> \
             <code>fn{}:{}</code> local{} via {}</li>",
            h.func_index,
            h.pc,
            h.local_index,
            esc(&h.via),
        );
    }
    s.push_str("</ul>");
    cap_note(s, r.handle_findings.len(), "handle faults");
    s.push_str("</section>");
}

/// FEAT-047: sound float-interval facts for f32/f64 locals — the analyzer no
/// longer treats float arithmetic as an opaque scope hole.
fn render_float_facts(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Float intervals (f32/f64)</h2>");
    if r.float_facts.is_empty() {
        s.push_str("<p class=\"empty\">No float-interval facts.</p></section>");
        return;
    }
    let _ = write!(
        s,
        "<p>{} sound float-interval fact(s).</p><ul class=\"diags\">",
        r.float_facts.len(),
    );
    for f in r.float_facts.iter().take(SECTION_ROW_CAP) {
        let _ = write!(
            s,
            "<li class=\"info\"><span class=\"sev\">f{}</span> \
             <code>fn{}:{}</code> local{} ∈ [{}, {}]{}</li>",
            f.width,
            f.func_index,
            f.pc,
            f.local_index,
            f.lo(),
            f.hi(),
            if f.nan { " ∪ NaN" } else { "" },
        );
    }
    s.push_str("</ul>");
    cap_note(s, r.float_facts.len(), "float facts");
    s.push_str("</section>");
}

/// FEAT-044: proven Pentagons strict relations — the `index < length` guards
/// scry recorded for an `if` then-region. Rendered as structured data (the
/// relational facts OOB-trap detection consumes), not silence.
fn render_pentagon_facts(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Relational guards (pentagons)</h2>");
    if r.pentagon_facts.is_empty() {
        s.push_str("<p class=\"empty\">No strict-less-than guards recorded.</p></section>");
        return;
    }
    let _ = write!(
        s,
        "<p>{} proven strict relation(s) (<code>x &lt; bound</code>) guarding an \
         <code>if</code> region.</p><ul class=\"diags\">",
        r.pentagon_facts.len(),
    );
    for f in r.pentagon_facts.iter().take(SECTION_ROW_CAP) {
        let sign = if f.unsigned { "u" } else { "s" };
        let _ = write!(
            s,
            "<li class=\"info\"><span class=\"sev\">lt_{sign}</span> \
             <code>fn{}:{}</code> local{} &lt; ",
            f.func_index, f.pc, f.lhs_local,
        );
        match f.bound {
            PentagonBound::Local(j) => {
                let _ = write!(s, "local{j}");
            }
            PentagonBound::Const(c) => {
                let _ = write!(s, "{c}");
            }
        }
        s.push_str("</li>");
    }
    s.push_str("</ul>");
    cap_note(s, r.pentagon_facts.len(), "relational guards");
    s.push_str("</section>");
}

fn render_diagnostics(s: &mut String, diags: &[Diagnostic]) {
    s.push_str("<section><h2>Diagnostics</h2>");
    if diags.is_empty() {
        s.push_str("<p class=\"empty\">No diagnostics.</p></section>");
        return;
    }
    s.push_str("<ul class=\"diags\">");
    for d in diags.iter().take(SECTION_ROW_CAP) {
        let (cls, label) = match d.severity {
            DiagnosticSeverity::Info => ("info", "info"),
            DiagnosticSeverity::Warning => ("warn", "warning"),
            DiagnosticSeverity::UnsoundnessFallback => ("err", "unsoundness-fallback"),
        };
        let _ = write!(
            s,
            "<li class=\"{cls}\"><span class=\"sev\">{label}</span> \
             <code>fn{}:{}</code> {}</li>",
            d.func_index,
            d.pc,
            esc(&d.message),
        );
    }
    s.push_str("</ul>");
    cap_note(s, diags.len(), "diagnostics");
    s.push_str("</section>");
}

/// If `total` exceeds [`SECTION_ROW_CAP`], append the "showing N of M" note that
/// every capped flat section shares.
fn cap_note(s: &mut String, total: usize, what: &str) {
    if total > SECTION_ROW_CAP {
        let _ = write!(
            s,
            "<p class=\"muted\">… showing {SECTION_ROW_CAP} of {total} {what}.</p>",
        );
    }
}

/// FEAT-030: taint (noninterference) findings. Rendered only when there ARE
/// findings — the scry-viz CLI runs with no taint policy, so the common case is
/// empty and a section would be noise; when present, each finding is a faithful
/// projection (escaped). A finding means a High (secret-dependent) value
/// reached a Low (public) sink.
fn render_taint(s: &mut String, r: &AnalysisResult) {
    if r.taint_findings.is_empty() {
        return;
    }
    s.push_str("<section><h2>Taint findings (noninterference)</h2>");
    s.push_str(
        "<table><thead><tr><th>func</th><th>pc</th><th>kind</th>\
         <th>source → sink</th><th>message</th></tr></thead><tbody>",
    );
    for f in &r.taint_findings {
        let kind = match f.kind {
            TaintFindingKind::HighResultExplicit => "explicit flow",
            TaintFindingKind::HighResultImplicit => "implicit flow",
        };
        let _ = write!(
            s,
            "<tr><td>{}</td><td>{}</td><td><span class=\"badge err\">{kind}</span></td>\
             <td>{} → {}</td><td>{}</td></tr>",
            fn_link(r, f.func_index),
            f.pc,
            label(&f.source_label),
            label(&f.sink_label),
            esc(&f.message),
        );
    }
    s.push_str("</tbody></table></section>");
}

/// A security label (`High`/`Low`) as a small styled span.
fn label(l: &SecurityLabel) -> &'static str {
    match l {
        SecurityLabel::High => "<span class=\"warn\">High</span>",
        SecurityLabel::Low => "<span class=\"ok\">Low</span>",
    }
}

/// FEAT-030: component provenance (FEAT-002) — the meld fusion origin map.
/// Rendered only when a `component-provenance` custom section was present and
/// decoded; absent for a plain Core Wasm module, so no section is emitted then.
fn render_provenance(s: &mut String, r: &AnalysisResult) {
    let Some(prov) = &r.provenance else { return };
    s.push_str("<section><h2>Component provenance</h2>");
    // FEAT-032: the fusion premises meld asserts by construction (v3 header).
    let yn = |b: bool| {
        if b {
            "<span class=\"ok\">yes</span>"
        } else {
            "<span class=\"muted\">no</span>"
        }
    };
    let _ = write!(
        s,
        "<dl><dt>fusion premises</dt><dd>bounded-memory: {} · closed-world: {}</dd>\
         <dt>fused module sha256</dt><dd><code>{}</code></dd></dl>",
        yn(prov.premises.bounded_memory),
        yn(prov.premises.closed_world),
        hex32(&prov.fused_module_sha256),
    );
    if prov.origins.is_empty() {
        s.push_str("<p class=\"empty\">No per-function origins.</p></section>");
        return;
    }
    s.push_str(
        "<p class=\"muted\">meld fusion origin map: each fused function traced \
         to its source component, original index, and code range.</p>",
    );
    s.push_str(
        "<table><thead><tr><th>fused func</th><th>component</th>\
         <th>original func</th><th>code range</th></tr></thead><tbody>",
    );
    for o in &prov.origins {
        let cr = match &o.code_range {
            Some(c) => format!("[{}, {})", c.start, c.end),
            None => "<span class=\"muted\">—</span>".to_string(),
        };
        let _ = write!(
            s,
            "<tr><td>{}</td><td><code>{}</code></td><td>{}</td><td>{cr}</td></tr>",
            fn_link(r, o.fused_func_index),
            esc(&o.component_id),
            o.orig_func_index,
        );
    }
    s.push_str("</tbody></table></section>");
}

/// Lowercase hex of a 32-byte hash.
fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for byte in b {
        let _ = write!(s, "{byte:02x}");
    }
    s
}

fn render_points(s: &mut String, r: &AnalysisResult) {
    let points = &r.invariants.points;
    s.push_str("<section><h2>Program points</h2>");
    if points.is_empty() {
        s.push_str("<p class=\"empty\">No program points.</p></section>");
        return;
    }
    // FEAT-027: group the points BY function ("where they sit") instead of one
    // flat table — each function gets an anchored subsection titled by its
    // name, so the Functions table's points-count and the call graph link here.
    let mut func_indices: Vec<u32> = points.iter().map(|p| p.func_index).collect();
    func_indices.sort_unstable();
    func_indices.dedup();
    let n_funcs = func_indices.len();

    // Compact summary over EVERY function (one cheap row each — small even for
    // scry-on-scry's ~800 functions). The detailed per-point tables below are
    // capped by function count AND points/function, or the section is a dump.
    let _ = write!(
        s,
        "<p class=\"muted\">{n_funcs} function(s) with program points — summary below; \
         detailed per-point invariants for the first {FUNCS_WITH_DETAIL_CAP}. The full \
         per-point data is scry's library <code>AnalysisResult</code>; the actionable \
         subset is in <code>guidance.json</code>.</p>\
         <table><thead><tr><th>function</th><th>points</th><th>max locals</th>\
         </tr></thead><tbody>",
    );
    for &idx in &func_indices {
        let fp = points.iter().filter(|p| p.func_index == idx);
        let count = fp.clone().count();
        let nloc = fp.map(|p| p.locals.len()).max().unwrap_or(0);
        let _ = write!(
            s,
            "<tr><td>{}</td><td>{count}</td><td>{nloc}</td></tr>",
            fn_link(r, idx),
        );
    }
    s.push_str("</tbody></table>");

    for &idx in func_indices.iter().take(FUNCS_WITH_DETAIL_CAP) {
        let heading = match fn_meta(r, idx).and_then(|m| m.name.as_deref()) {
            Some(n) => format!("func {idx} · {}", name_span(&demangle(n))),
            None => format!("func {idx}"),
        };
        let fn_points: Vec<_> = points.iter().filter(|p| p.func_index == idx).collect();
        let n_points = fn_points.len();
        let n_locals = fn_points.iter().map(|p| p.locals.len()).max().unwrap_or(0);
        let _ = write!(
            s,
            "<h3 id=\"pts-{idx}\" class=\"fn-points\">{heading} \
             <a class=\"backref\" href=\"#fn-{idx}\">↑ row</a></h3>\
             <p class=\"muted\">{n_points} program point(s) · up to {n_locals} local(s) tracked.</p>",
        );
        s.push_str(
            "<table><thead><tr><th>pc</th><th>locals</th>\
             <th>operand stack (bottom → top)</th>\
             <th>memory (offset → value)</th></tr></thead><tbody>",
        );
        for p in fn_points.iter().take(POINTS_PER_FN_CAP) {
            let locals = if p.locals.is_empty() {
                "(none)".to_string()
            } else {
                p.locals
                    .iter()
                    .map(|l| format!("L{}={}", l.local_index, abstract_value(&l.value)))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            // FEAT-023: the abstract operand stack. Empty is shown as "(empty)"
            // — the analyzer's honest "no operand-stack info here", not a claim
            // that the concrete stack is empty.
            let stack = if p.operand_stack.is_empty() {
                "<span class=\"empty\">(empty)</span>".to_string()
            } else {
                p.operand_stack
                    .iter()
                    .map(abstract_value)
                    .collect::<Vec<_>>()
                    .join(" · ")
            };
            // FEAT-062: the tracked linear-memory content (FEAT-058). Empty is
            // shown as "(⊤)" — the analyzer's honest "no content tracked here",
            // not a claim that memory is empty. A single-byte cell [o,o+1) (the
            // strong-store case) renders as "@o"; a wider cell as "[lo, hi)".
            let mem = if p.memory.is_empty() {
                "<span class=\"empty\">(⊤)</span>".to_string()
            } else {
                p.memory
                    .iter()
                    .map(|m| {
                        let loc = if m.hi == m.lo + 1 {
                            format!("@{}", m.lo)
                        } else {
                            format!("[{}, {})", m.lo, m.hi)
                        };
                        format!("{loc}={}", interval(&m.value))
                    })
                    .collect::<Vec<_>>()
                    .join(" · ")
            };
            let _ = write!(
                s,
                "<tr><td>{}</td><td><code>{}</code></td><td><code>{}</code></td>\
                 <td><code>{}</code></td></tr>",
                p.pc,
                esc(&locals),
                stack,
                mem,
            );
        }
        s.push_str("</tbody></table>");
        if n_points > POINTS_PER_FN_CAP {
            let _ = write!(
                s,
                "<p class=\"muted\">… showing {} of {} points for this function \
                 (full per-point invariants are scry's library output).</p>",
                POINTS_PER_FN_CAP, n_points,
            );
        }
    }
    s.push_str("</section>");
}

// ── FEAT-031: well-formedness oracle ───────────────────────────────────────

/// The interval inside an [`AbstractValue`], if it carries one.
fn interval_of(v: &AbstractValue) -> Option<&Interval> {
    match v {
        AbstractValue::I32Interval(iv) | AbstractValue::I64Interval(iv) => Some(iv),
        AbstractValue::RegionPointer(Region { offset, .. }) => Some(offset),
        AbstractValue::Unknown => None,
    }
}

/// FEAT-031: structural well-formedness checks on an `AnalysisResult` —
/// invariants the analyzer must ALWAYS satisfy regardless of input. Returns the
/// list of violations (empty ⇒ well-formed). `scry-viz check` runs this on
/// scry's OWN compiled module in CI as a robustness gate: a violation is a scry
/// bug, and fails the build. This is structural validation (e.g. no inverted
/// `[lo,hi]` interval), NOT a soundness oracle — soundness is the host tests'
/// and proofs' job.
pub fn check_wellformed(r: &AnalysisResult) -> Vec<String> {
    let mut v = Vec::new();
    if r.invariants.schema.is_empty() {
        v.push("invariants.schema is empty".to_string());
    }
    let sha = &r.invariants.module_sha256;
    if sha.len() != 64 || !sha.bytes().all(|b| b.is_ascii_hexdigit()) {
        v.push(format!("module_sha256 is not 64 hex chars: {sha:?}"));
    }
    let check_iv = |whr: String, val: &AbstractValue, out: &mut Vec<String>| {
        if let Some(iv) = interval_of(val)
            && iv.lo > iv.hi
        {
            out.push(format!("{whr}: inverted interval [{}, {}]", iv.lo, iv.hi));
        }
    };
    for p in &r.invariants.points {
        for l in &p.locals {
            check_iv(
                format!("fn{} pc{} L{}", p.func_index, p.pc, l.local_index),
                &l.value,
                &mut v,
            );
        }
        for (i, sv) in p.operand_stack.iter().enumerate() {
            check_iv(
                format!("fn{} pc{} stack{i}", p.func_index, p.pc),
                sv,
                &mut v,
            );
        }
    }
    for fs in &r.function_summaries {
        for (i, sv) in fs.result_summary.iter().enumerate() {
            check_iv(format!("fn{} result{i}", fs.func_index), sv, &mut v);
        }
    }
    // FEAT-027 metadata must be index-ordered and gapless.
    for (i, m) in r.function_meta.iter().enumerate() {
        if m.func_index as usize != i {
            v.push(format!(
                "function_meta not gapless/sorted at position {i}: func_index {}",
                m.func_index
            ));
            break;
        }
    }
    // FEAT-022: reachable set is documented sorted ascending.
    if !r.reachable_from_exports.is_sorted() {
        v.push("reachable_from_exports is not sorted ascending".to_string());
    }
    v
}

// ── value formatting ─────────────────────────────────────────────────────

/// Render an [`AbstractValue`] compactly. A singleton interval `[n,n]` shows as
/// `n` (a known constant); a wider interval as `[lo,hi]`.
fn abstract_value(v: &AbstractValue) -> String {
    match v {
        AbstractValue::I32Interval(iv) => format!("i32 {}", interval(iv)),
        AbstractValue::I64Interval(iv) => format!("i64 {}", interval(iv)),
        AbstractValue::RegionPointer(Region { region_id, offset }) => {
            format!("region#{region_id}+{}", interval(offset))
        }
        AbstractValue::Unknown => "⊤".to_string(),
    }
}

fn interval(iv: &Interval) -> String {
    if iv.lo == iv.hi {
        iv.lo.to_string()
    } else {
        format!("[{}, {}]", iv.lo, iv.hi)
    }
}

fn stack_bound(b: &StackBound) -> String {
    match b {
        StackBound::Bytes(n) => format!("{n} bytes"),
        StackBound::Unbounded => "unbounded".to_string(),
        StackBound::Unknown => "unknown".to_string(),
    }
}

fn yesno(b: bool) -> &'static str {
    if b {
        "<span class=\"ok\">yes</span>"
    } else {
        "<span class=\"muted\">no</span>"
    }
}

fn kv(s: &mut String, k: &str, v: &str) {
    let _ = write!(s, "<dt>{}</dt><dd>{}</dd>", esc(k), esc(v));
}

/// Minimal HTML-text escaping for the few attacker-influenced strings we render
/// (diagnostic messages, schema URL). Covers the five significant characters.
fn esc(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len());
    for c in raw.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

// ── structured guidance feed ────────────────────────────────────────────────

/// FEAT-068: the guidance-feed schema version. Bumped when a field is added or
/// its meaning changes, so a consumer can tell "this producer is old" from
/// "this module has no such finding" — the distinction the un-versioned v1 feed
/// could not express.
///
/// v2 added `guidance_schema` itself plus `obligation_id`, `site_key` and
/// `group_key` on every advisory.
///
/// v3 (FEAT-076, scry#123) adds `id_build_local` on every advisory: `true`
/// means the three identity keys are unique within THIS analysis but NOT
/// comparable across builds (the function's stripped name is shared by
/// another function, so the raw, disambiguated — and churning — name is
/// hashed). A consumer diffing two runs must skip such advisories rather than
/// read the churn as discharged/new obligations.
pub const GUIDANCE_SCHEMA_VERSION: u32 = 3;

/// Serialize the actionable findings as a machine-consumable JSON document — the
/// feed an AI-agent consumer reads instead of scraping the (now capped) HTML.
///
/// Shape: a top-level object
/// `{ "guidance_schema": 3, "module_sha256": "…", "schema": "…",
///    "advisories": [ … ], "trap_checks": [ … ] }`.
///
/// FEAT-068: `guidance_schema` is an explicit integer version. v1 (the v3.2.2
/// feed) had none, so a consumer could not tell a field's ABSENCE from an old
/// producer. v2 adds the version and the three FEAT-064/DD-021 identity keys;
/// v3 (FEAT-076) adds `id_build_local`. Absence of `guidance_schema` means
/// v1; a consumer requiring identity must check for it rather than assume.
///
/// Each advisory is
/// `{ "func_index", "pc", "class", "code", "detail", "suggested_action",
///    "verification", "obligation_id", "site_key", "group_key",
///    "id_build_local", "counterexample"? }`, mirroring the [`Advisory`] fields
/// (`class` uses the machine-stable name, e.g. `"unproven-obligation"`). Each
/// trap check is `{ "func_index", "pc", "op", "kind", "verdict" }`.
///
/// The crate has no serde dependency, so this is hand-rolled with proper JSON
/// string escaping ([`json_esc`]) — the full (un-capped) set is emitted, unlike
/// the HTML.
pub fn render_guidance_json(result: &AnalysisResult) -> String {
    let mut s = String::with_capacity(4 * 1024);
    s.push('{');
    let _ = write!(
        s,
        "\"guidance_schema\":{},\"module_sha256\":\"{}\",\"schema\":\"{}\",",
        GUIDANCE_SCHEMA_VERSION,
        json_esc(&result.invariants.module_sha256),
        json_esc(&result.invariants.schema),
    );
    // advisories
    s.push_str("\"advisories\":[");
    for (i, a) in result.advisories.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(
            s,
            "{{\"func_index\":{},\"pc\":{},\"class\":\"{}\",\"code\":\"{}\",\
             \"detail\":\"{}\",\"suggested_action\":\"{}\",\"verification\":\"{}\",\
             \"obligation_id\":\"{}\",\"site_key\":\"{}\",\"group_key\":\"{}\",\
             \"id_build_local\":{}",
            a.func_index,
            a.pc,
            advisory_class_name(a.class),
            json_esc(&a.code),
            json_esc(&a.detail),
            json_esc(&a.suggested_action),
            json_esc(&a.verification),
            json_esc(&a.obligation_id),
            json_esc(&a.site_key),
            json_esc(&a.group_key),
            a.id_build_local,
        );
        if let Some(cx) = &a.counterexample {
            let _ = write!(
                s,
                ",\"counterexample\":{{\"trigger\":\"{}\",\"witness\":[",
                json_esc(&cx.trigger)
            );
            for (j, w) in cx.witness.iter().enumerate() {
                if j > 0 {
                    s.push(',');
                }
                let _ = write!(
                    s,
                    "{{\"operand\":\"{}\",\"value\":{}}}",
                    json_esc(&w.operand),
                    w.value,
                );
            }
            s.push_str("]}");
        }
        s.push('}');
    }
    s.push_str("],");
    // trap checks
    s.push_str("\"trap_checks\":[");
    for (i, t) in result.trap_checks.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let kind = match t.kind {
            TrapKind::DivByZero => "div-by-zero",
            TrapKind::SignedOverflow => "signed-overflow",
            TrapKind::OutOfBounds => "out-of-bounds",
        };
        let verdict = match t.verdict {
            TrapVerdict::ProvenSafe => "proven-safe",
            TrapVerdict::PotentialTrap => "potential-trap",
        };
        let _ = write!(
            s,
            "{{\"func_index\":{},\"pc\":{},\"op\":\"{}\",\"kind\":\"{}\",\"verdict\":\"{}\"}}",
            t.func_index,
            t.pc,
            json_esc(&t.op),
            kind,
            verdict,
        );
    }
    s.push_str("]}");
    s
}

/// JSON string-content escaping (RFC 8259): the two mandatory escapes `"` and
/// `\`, plus all control chars U+0000–U+001F as `\uXXXX` (with the short forms
/// for the common ones). The caller supplies the surrounding quotes.
fn json_esc(raw: &str) -> String {
    let mut out = String::with_capacity(raw.len() + 2);
    for c in raw.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out
}

const DOCTYPE_AND_HEAD_OPEN: &str = "<!DOCTYPE html><html lang=\"en\"><head>\
    <meta charset=\"utf-8\"><meta name=\"viewport\" \
    content=\"width=device-width, initial-scale=1\">";

const STYLE: &str = "<style>\
    :root{--fg:#1a1a1a;--muted:#777;--ok:#0a7d33;--warn:#b35900;--err:#b00020;\
    --line:#e0e0e0;--bg:#fff;--code:#f4f4f6}\
    body{font:14px/1.5 -apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;\
    color:var(--fg);background:var(--bg);margin:0 auto;max-width:1100px;padding:24px}\
    h1{font-size:22px}h2{font-size:17px;margin-top:32px;border-bottom:2px solid var(--line);\
    padding-bottom:4px}\
    table{border-collapse:collapse;width:100%;margin:8px 0;font-size:13px}\
    th,td{text-align:left;padding:5px 9px;border-bottom:1px solid var(--line);vertical-align:top}\
    th{background:#fafafa;font-weight:600}\
    code{background:var(--code);padding:1px 4px;border-radius:3px;font-size:12px}\
    dl{display:grid;grid-template-columns:max-content 1fr;gap:2px 16px;margin:8px 0}\
    dt{color:var(--muted)}dd{margin:0;font-variant-numeric:tabular-nums}\
    .ok{color:var(--ok);font-weight:600}.warn{color:var(--warn);font-weight:600}\
    .err{color:var(--err);font-weight:600}.muted,.empty{color:var(--muted)}\
    .diags{list-style:none;padding:0}.diags li{padding:4px 0;border-bottom:1px solid var(--line)}\
    .anchor{float:right;color:var(--line);text-decoration:none;font-weight:400;\
    padding:0 2px;margin-left:8px}\
    .diags li:hover .anchor{color:var(--muted)}.anchor:hover{color:var(--fg)}\
    .diags li:target{background:#fffbe6;outline:2px solid #f0d98a;outline-offset:2px;\
    scroll-margin-top:16px}\
    .diags li:target .anchor{color:var(--fg)}\
    .badge{display:inline-block;font-size:11px;padding:1px 6px;border-radius:10px;\
    border:1px solid var(--line);white-space:nowrap}\
    .badge.import{background:#eef4ff;border-color:#cdd9f0}\
    .badge.export{background:#eafaf0;border-color:#c5e8d2}\
    .badge.lang{background:#f3eefe;border-color:#ddd0f5}\
    .badge.err{background:#fdecef;border-color:#f3c2cc;color:var(--err)}\
    .nm{display:inline-block;max-width:42ch;overflow:hidden;text-overflow:ellipsis;\
    white-space:nowrap;vertical-align:bottom;font-family:ui-monospace,Menlo,monospace;\
    font-size:12px}\
    td .nm{max-width:38ch}h3 .nm{max-width:60ch}\
    h3.fn-points{font-size:14px;margin:22px 0 4px;scroll-margin-top:8px}\
    tr[id^=\"fn-\"]{scroll-margin-top:8px}\
    .backref{font-size:11px;font-weight:400;text-decoration:none;color:var(--muted)}\
    svg.cg{max-width:100%;height:auto;border:1px solid var(--line);border-radius:6px;\
    background:#fff;margin:6px 0}\
    svg.cg .nd rect{fill:#fafafa;stroke:#bbb}\
    svg.cg .nd.imp rect{fill:#eef4ff;stroke:#cdd9f0}\
    svg.cg .nd.exp rect{stroke:#0a7d33;stroke-width:1.5}\
    svg.cg .nd text{font:12px ui-monospace,Menlo,monospace;fill:var(--fg)}\
    svg.cg .e{fill:none;stroke:#999;stroke-width:1.3}\
    svg.cg .e.ind{stroke-dasharray:5 4}\
    svg.cg .e.uns{stroke:var(--err);stroke-width:1.6}\
    pre.mermaid-src{background:var(--code);padding:10px;border-radius:4px;overflow:auto;\
    font-size:12px;white-space:pre}\
    details{margin:6px 0}summary{cursor:pointer;color:var(--muted);font-size:13px}\
    .cards{list-style:none;padding:0;display:grid;gap:12px;max-width:640px}\
    .cards li{border:1px solid var(--line);border-radius:6px;padding:14px 16px}\
    .cards a{font-size:16px;text-decoration:none}.cards a:hover{text-decoration:underline}\
    .sev{font-size:11px;text-transform:uppercase;font-weight:700;margin-right:6px}\
    .info .sev{color:var(--muted)}.warn .sev{color:var(--warn)}.err .sev{color:var(--err)}\
    footer{margin-top:40px;color:var(--muted);font-size:12px}\
    </style>";

#[cfg(test)]
mod tests {
    use super::*;
    use scry_analyze_core::{AnalysisConfig, analyze};

    fn analyze_wat(src: &str) -> AnalysisResult {
        let bytes = wat::parse_str(src).expect("assemble wat");
        analyze(bytes, AnalysisConfig::default()).expect("analyze")
    }

    #[test]
    fn renders_memory_content_cell() {
        // FEAT-062: the tracked memory content (FEAT-058) must be visible in the
        // rendered page — a store of 42 @16 then load surfaces the [16,17)→42
        // cell, rendered "@16=42" under the "memory" column.
        let r = analyze_wat(
            "(module (memory 1) (func (export \"run\") (result i32) (local i32) \
             i32.const 16 i32.const 42 i32.store \
             i32.const 16 i32.load local.set 0 local.get 0))",
        );
        let html = render_html(&r, "mem");
        assert!(
            html.contains("memory (offset → value)"),
            "the program-points table must carry a memory column"
        );
        assert!(
            html.contains("@16=42"),
            "the tracked cell [16,17)→42 must render as @16=42; html omitted it"
        );
    }

    #[test]
    fn renders_operand_stack_constants() {
        // The FEAT-023 showcase: a known constant on the operand stack must
        // appear verbatim in the rendered page.
        let r = analyze_wat(
            "(module (func (export \"run\") (result i32) \
             i32.const 42 i32.const 7 i32.add))",
        );
        let html = render_html(&r, "demo");
        assert!(html.starts_with("<!DOCTYPE html>"), "is an HTML document");
        assert!(html.contains("Program points"), "has the points section");
        // The singleton constants from the operand stack are projected verbatim.
        assert!(
            html.contains("operand stack"),
            "labels the operand-stack column"
        );
        assert!(
            html.contains("i32 42"),
            "the constant 42 appears on the stack"
        );
        assert!(
            html.contains("i32 49"),
            "the i32.add result 49 appears on the stack"
        );
    }

    #[test]
    fn renders_empty_operand_stack_honestly() {
        // `local.get 0; local.set 0` drains the stack, so the point emitted
        // after `local.set` has an empty operand stack — it must render as
        // "(empty)", not be silently dropped or mislabelled.
        let r = analyze_wat(
            "(module (func (export \"run\") (param i32) \
             local.get 0 local.set 0))",
        );
        let html = render_html(&r, "drain");
        assert!(
            html.contains("(empty)"),
            "empty operand stack rendered honestly"
        );
    }

    #[test]
    fn escapes_untrusted_text() {
        // Diagnostic/schema strings must be HTML-escaped, never injected raw.
        let r = analyze_wat("(module (func (export \"run\") nop))");
        let html = render_html(&r, "<script>alert(1)</script>");
        assert!(
            !html.contains("<script>alert(1)</script>"),
            "title is escaped"
        );
        assert!(html.contains("&lt;script&gt;"), "escaped form present");
    }

    #[test]
    fn index_links_entries_and_escapes() {
        let html = render_index(
            "scry v1.15.0",
            &[
                IndexEntry {
                    href: "self-analysis.html".into(),
                    title: "Self-analysis".into(),
                    description: "scry analyzing its own module".into(),
                },
                IndexEntry {
                    href: "mcdc/index.html".into(),
                    title: "MC/DC dashboard".into(),
                    description: "truth tables".into(),
                },
            ],
        );
        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(
            html.contains("href=\"self-analysis.html\""),
            "links self-analysis"
        );
        assert!(
            html.contains("href=\"mcdc/index.html\""),
            "links MC/DC dashboard"
        );
        assert!(html.contains("scry v1.15.0"), "shows the site title");
        assert!(html.ends_with("</html>"));
    }

    #[test]
    fn index_escapes_untrusted_entry_fields() {
        let html = render_index(
            "<b>x</b>",
            &[IndexEntry {
                href: "\"></a><script>".into(),
                title: "<script>".into(),
                description: "&".into(),
            }],
        );
        assert!(
            !html.contains("<script>"),
            "no raw script tag from entry fields"
        );
        assert!(html.contains("&lt;script&gt;"), "escaped form present");
    }

    #[test]
    fn renders_function_names_kinds_and_grouped_points() {
        // FEAT-027: an imported $log, a defined+exported $compute calling
        // $helper. The viz must show names, kind badges, named call-graph
        // links, and per-function point groups.
        let r = analyze_wat(
            "(module (import \"env\" \"log\" (func $log (param i32))) \
             (func $compute (export \"run\") (result i32) call $helper i32.const 7) \
             (func $helper nop))",
        );
        let html = render_html(&r, "named");
        // Names appear (from the name section).
        assert!(html.contains("compute"), "defined function name shown");
        assert!(html.contains("helper"), "callee name shown");
        // Kind badges.
        assert!(
            html.contains("class=\"badge import\">import"),
            "import badge"
        );
        assert!(html.contains("export \"run\""), "export badge with name");
        // The functions table row is anchored, and the call graph links to it.
        assert!(html.contains("id=\"fn-2\""), "function row anchored");
        assert!(
            html.contains("href=\"#fn-2\""),
            "call graph / points link to the function row"
        );
        // Program points are grouped per function under an anchored heading.
        assert!(
            html.contains("id=\"pts-1\""),
            "per-function points group anchored"
        );
    }

    #[test]
    fn renders_callgraph_diagram_svg_and_mermaid() {
        // FEAT-028: $compute calls $helper → one resolved edge. The diagram is
        // small, so we get inline SVG + a Mermaid source block.
        let r = analyze_wat(
            "(module (func $compute (export \"run\") (result i32) call $helper i32.const 7) \
             (func $helper nop))",
        );
        let html = render_html(&r, "diagram");
        assert!(
            html.contains("Call-graph diagram"),
            "diagram section present"
        );
        // Inline SVG, self-contained (no <script>, no external src=).
        assert!(html.contains("<svg class=\"cg\""), "inline SVG drawn");
        assert!(!html.contains("<script"), "no JavaScript");
        assert!(!html.contains("src=\"http"), "no external assets");
        // Nodes carry the resolved names; the edge is in the Mermaid source.
        assert!(html.contains("Mermaid source"), "mermaid export present");
        assert!(html.contains("graph LR"), "mermaid graph definition");
        assert!(
            html.contains("--&gt;"),
            "a direct edge in the (escaped) mermaid source"
        );
    }

    #[test]
    fn callgraph_diagram_handles_no_resolved_edges() {
        // A lone function with no calls → no edges → an honest note, no SVG,
        // no panic.
        let r = analyze_wat("(module (func (export \"run\") nop))");
        let html = render_html(&r, "noedges");
        assert!(html.contains("No call edges.") || html.contains("No resolved call edges"));
        assert!(html.ends_with("</html>"));
    }

    #[test]
    fn demangles_rust_legacy_v0_and_leaves_plain() {
        // FEAT-029: name-section symbols (modelled via quoted wat ids) are
        // demangled for display; a plain name is left as-is with no language.
        let r = analyze_wat(
            "(module \
             (func $\"_ZN9scry_mcdc5drive17h16e8a19d4dbffa6cE\" (export \"a\") nop) \
             (func $\"_RNvNtCsi9YzqDQQz2q_5alloc3fmt6format\" (export \"b\") nop) \
             (func $calloc (export \"c\") nop))",
        );
        let html = render_html(&r, "demangle");
        // Rust legacy `_ZN…E` → `scry_mcdc::drive` (hash stripped from the
        // DISPLAY — the display text ends at the name, no `…17h<hash>` glued
        // on; the raw symbol with the hash is kept only on hover, below).
        assert!(html.contains("scry_mcdc::drive"), "rust legacy demangled");
        assert!(
            html.contains("scry_mcdc::drive</span>"),
            "display ends at the demangled name (hash stripped)"
        );
        // Rust v0 `_R…` → `alloc::fmt::format`.
        assert!(html.contains("alloc::fmt::format"), "rust v0 demangled");
        // A language tag appears for the demangled ones.
        assert!(html.contains("badge lang\">rust"), "rust language tag");
        // Plain C-style name is unchanged (and not tagged with a language).
        assert!(html.contains("calloc"), "plain name preserved");
        // The raw symbol is preserved on hover (title carries `[symbol] …`).
        assert!(
            html.contains("[symbol] _ZN9scry_mcdc5drive"),
            "raw symbol kept on hover"
        );
    }

    #[test]
    fn demangled_generic_name_is_escaped() {
        // A Rust generic demangles to a name containing `<…>`; it must be
        // HTML-escaped wherever shown.
        let r = analyze_wat(
            "(module (func \
             $\"_ZN4core3ptr54drop_in_place$LT$scry_analyze_core..AnalysisResult$GT$17h40256ad9d7a94464E\" \
             (export \"d\") nop))",
        );
        let html = render_html(&r, "generic");
        assert!(
            html.contains("drop_in_place&lt;"),
            "demangled generic angle-brackets escaped"
        );
        assert!(!html.contains("drop_in_place<scry"), "no raw < emitted");
    }

    #[test]
    fn long_name_uses_ellipsis_class_with_hover() {
        // Long demangled names are shortened in place (CSS .nm ellipsis) with
        // the full form in the title hover.
        let r = analyze_wat(
            "(module (func \
             $\"_ZN4core3ptr54drop_in_place$LT$scry_analyze_core..AnalysisResult$GT$17h40256ad9d7a94464E\" \
             (export \"d\") nop))",
        );
        let html = render_html(&r, "long");
        assert!(
            html.contains("<span class=\"nm\""),
            "name uses the ellipsizable .nm span"
        );
        assert!(html.contains("title=\""), "full name available on hover");
    }

    #[test]
    fn function_names_html_escaped() {
        // A name with HTML metacharacters must be escaped wherever it's shown.
        // (wat allows arbitrary quoted ids.)
        let r = analyze_wat("(module (func $\"<x>\" (export \"e\") nop))");
        let html = render_html(&r, "esc");
        assert!(!html.contains("<x>"), "raw name not injected");
        assert!(html.contains("&lt;x&gt;"), "name escaped");
    }

    #[test]
    fn renders_taint_findings_when_present() {
        // FEAT-030: with a taint policy (High param 0 → Low result 0), a
        // leaking function produces a finding the viz now surfaces.
        let bytes = wat::parse_str(
            "(module (func (export \"leak\") (param i32) (result i32) local.get 0))",
        )
        .unwrap();
        let cfg = scry_analyze_core::AnalysisConfig {
            widening_threshold: Some(3),
            emit_diagnostics: true,
            taint_policy: Some(scry_analyze_core::TaintPolicy {
                high_params: alloc_vec(0),
                low_results: alloc_vec(0),
            }),
        };
        let r = scry_analyze_core::analyze(bytes, cfg).unwrap();
        assert!(!r.taint_findings.is_empty(), "policy must yield a finding");
        let html = render_html(&r, "taint");
        assert!(html.contains("Taint findings"), "taint section present");
        assert!(html.contains("explicit flow"), "finding kind shown");
        assert!(html.contains(">High<"), "source label shown");
        assert!(html.contains(">Low<"), "sink label shown");
    }

    fn alloc_vec(x: u32) -> Vec<u32> {
        vec![x]
    }

    #[test]
    fn no_taint_or_provenance_section_when_absent() {
        // FEAT-030: the common case (no taint policy, plain Core Wasm) shows
        // neither section — they are surfaced only when present, not as clutter.
        let r = analyze_wat("(module (func (export \"run\") nop))");
        let html = render_html(&r, "plain");
        assert!(
            !html.contains("Taint findings"),
            "no taint section when empty"
        );
        assert!(
            !html.contains("Component provenance"),
            "no provenance section when absent"
        );
    }

    #[test]
    fn check_wellformed_passes_on_real_module() {
        // FEAT-031: a normally-analyzed module is well-formed — the gate must
        // not false-positive.
        for fx in [
            "fixture-11-var-bound.wat",
            "fixture-18-operand-stack.wat",
            "fixture-19-named-functions.wat",
        ] {
            let r = analyze_fixture(fx);
            let v = check_wellformed(&r);
            assert!(v.is_empty(), "{fx} should be well-formed, got {v:?}");
        }
    }

    fn analyze_fixture(name: &str) -> AnalysisResult {
        let path = format!(
            "{}/../scry-analyzer/test-fixtures/{name}",
            env!("CARGO_MANIFEST_DIR")
        );
        let bytes = wat::parse_file(&path).expect("assemble fixture");
        analyze(bytes, AnalysisConfig::default()).expect("analyze")
    }

    #[test]
    fn check_wellformed_flags_an_inverted_interval() {
        // Inject an impossible interval [5,1] and confirm the gate catches it.
        let mut r = analyze_wat("(module (func (export \"run\") (result i32) i32.const 7))");
        let bad = scry_analyze_core::AbstractValue::I32Interval(scry_analyze_core::Interval {
            lo: 5,
            hi: 1,
        });
        // Attach it to a program point's operand stack.
        assert!(!r.invariants.points.is_empty());
        r.invariants.points[0].operand_stack.push(bad);
        let v = check_wellformed(&r);
        assert!(
            v.iter().any(|m| m.contains("inverted interval [5, 1]")),
            "gate must flag the inverted interval, got {v:?}"
        );
    }

    #[test]
    fn no_panic_on_empty_module() {
        let r = analyze_wat("(module)");
        let html = render_html(&r, "empty");
        assert!(html.contains("No functions.") || html.contains("Functions"));
        assert!(html.ends_with("</html>"));
    }

    #[test]
    fn hero_and_scope_copy_finalized() {
        // Retitle away from bare "verification dashboard", and the scope block
        // carries the precise soundness copy (mechanized vs γ-swept, ⊤=unknown).
        let r = analyze_wat("(module (func (export \"run\") nop))");
        let html = render_html(&r, "demo");
        // No leftover placeholders.
        assert!(
            !html.contains("SCOPE_TAGLINE_PLACEHOLDER"),
            "tagline filled"
        );
        assert!(
            !html.contains("SCOPE_COPY_PLACEHOLDER"),
            "scope copy filled"
        );
        assert!(!html.contains("verification dashboard"), "retitled");
        // Precise, scoped claims present.
        assert!(
            html.contains("sound static analyzer for WebAssembly"),
            "hero states the scoped claim"
        );
        assert!(
            html.contains("<section id=\"scope\">"),
            "scope section present"
        );
        assert!(html.contains("Scope &amp; limitations"), "scope heading");
        assert!(
            html.contains("Mechanized (Rocq, admit-free"),
            "evidence-kind: mechanized"
        );
        assert!(
            html.contains("γ-sweep-validated (tested, NOT mechanized)"),
            "evidence-kind: γ-swept vs mechanized distinction is legible"
        );
        assert!(
            html.contains("never \"safe\""),
            "the ⊤=unknown-not-safe soundness caveat is stated"
        );
    }

    #[test]
    fn points_section_is_capped_and_page_stays_small() {
        // Page-size sanity: scry-on-scry has ~800 FUNCTIONS each with points, so
        // a per-function cap alone is not enough (800 × 20 rows is still ~10 MB).
        // Synthesize points across many functions and assert (a) only the first
        // `FUNCS_WITH_DETAIL_CAP` functions get a detailed table, and (b) the
        // whole page stays well under 1 MB.
        let mut r = analyze_wat(
            "(module (func (export \"run\") (result i32) i32.const 42 i32.const 7 i32.add))",
        );
        let template = r.invariants.points[0].clone();
        r.invariants.points.clear();
        const FUNCS: u32 = 500;
        const PTS_PER_FN: u32 = 30;
        for f in 0..FUNCS {
            for pc in 0..PTS_PER_FN {
                let mut p = template.clone();
                p.func_index = f;
                p.pc = pc;
                r.invariants.points.push(p);
            }
        }
        assert_eq!(r.invariants.points.len() as u32, FUNCS * PTS_PER_FN);
        let html = render_html(&r, "big");
        // Every function appears in the cheap summary line …
        assert!(
            html.contains("function(s) with program points"),
            "per-function summary present"
        );
        // … but only the first FUNCS_WITH_DETAIL_CAP get a detailed table.
        let detailed = html.matches("class=\"fn-points\"").count();
        assert!(
            detailed <= FUNCS_WITH_DETAIL_CAP,
            "detailed tables capped at {FUNCS_WITH_DETAIL_CAP}, got {detailed}"
        );
        // … and the whole page stays under 1 MB despite 15k points / 500 funcs.
        assert!(
            html.len() < 1_000_000,
            "page must stay under 1 MB across many functions; was {} bytes",
            html.len()
        );
    }

    #[test]
    fn all_flat_sections_capped_page_stays_small() {
        // The lesson from v3.2.2/v3.2.3: capping ONE section is not enough — the
        // deployed self-analysis was still ~5 MB from Diagnostics / Call graph /
        // Trap checks. This test blows up EVERY large flat section and asserts
        // the whole page stays under 1 MB, so a future uncapped section fails
        // here instead of on the deployed site.
        let mut r = analyze_wat(
            "(module (memory 1) (func $h) \
             (func (export \"run\") (param i32) (result i32) \
               i32.const 4 i32.const 0 i32.store \
               call $h \
               i32.const 10 local.get 0 i32.div_s))",
        );
        fn blow<T: Clone>(v: &mut Vec<T>, n: usize) {
            if let Some(first) = v.first().cloned() {
                while v.len() < n {
                    v.push(first.clone());
                }
            }
        }
        blow(&mut r.diagnostics, 4000);
        blow(&mut r.trap_checks, 4000);
        blow(&mut r.call_graph, 4000);
        blow(&mut r.advisories, 4000);
        blow(&mut r.gaps, 4000);
        blow(&mut r.handle_findings, 4000);
        blow(&mut r.float_facts, 4000);
        blow(&mut r.pentagon_facts, 4000);
        let html = render_html(&r, "big-all");
        assert!(
            html.len() < 1_000_000,
            "every flat section must be capped so the page stays <1 MB; was {} bytes",
            html.len()
        );
        // Cap notes prove the sections were actually large-but-capped.
        assert!(html.contains("… showing 100 of"), "cap notes present");
    }

    #[test]
    fn guidance_json_is_well_formed_and_carries_advisories() {
        // A div by an unknown divisor yields an UnprovenObligation advisory +
        // a POTENTIAL-TRAP check; both must appear in the JSON feed, and the
        // document must be structurally well-formed JSON.
        let r = analyze_wat(
            "(module (func (export \"run\") (param i32) (result i32) \
             i32.const 10 local.get 0 i32.div_s))",
        );
        assert!(
            !r.advisories.is_empty(),
            "fixture must produce at least one advisory"
        );
        let json = render_guidance_json(&r);
        assert!(json.starts_with('{') && json.ends_with('}'), "JSON object");
        assert!(json.contains("\"advisories\":["), "advisories array");
        assert!(json.contains("\"trap_checks\":["), "trap_checks array");
        assert!(json.contains("\"module_sha256\":\""), "carries module hash");
        // The class name is the machine-stable form.
        assert!(
            json.contains("\"class\":\"unproven-obligation\""),
            "expected advisory class present, json was: {json}"
        );
        assert!(json.contains("\"code\":\""), "advisory code field present");
        assert!(json.contains("\"verification\":\""), "verification field");
        // Structural well-formedness: balanced braces/brackets and balanced
        // quotes (accounting for escapes).
        assert_json_balanced(&json);
    }

    #[test]
    fn guidance_json_escapes_control_and_quote_chars() {
        // The JSON escaper must handle `"`, `\`, and control chars. We drive an
        // advisory through and additionally unit-test the escaper directly.
        assert_eq!(json_esc("a\"b\\c"), "a\\\"b\\\\c");
        assert_eq!(json_esc("line\nbreak\ttab"), "line\\nbreak\\ttab");
        assert_eq!(json_esc("\u{01}"), "\\u0001");
    }

    #[test]
    fn guidance_html_collapses_boilerplate_but_keeps_faults() {
        // The Guidance panel keeps the tally line and does not inline thousands
        // of identical non-fault rows: with more than the cap of one non-fault
        // class, a "… and N more" line must appear.
        let mut r = analyze_wat("(module (func (export \"run\") nop))");
        // Synthesize many UnprovenObligation advisories.
        let mk = |i: u32| scry_analyze_core::Advisory {
            func_index: 0,
            pc: i,
            class: AdvisoryClass::UnprovenObligation,
            code: "div-by-zero".into(),
            detail: "divisor may be zero".into(),
            suggested_action: "guard it".into(),
            verification: "re-run scry".into(),
            counterexample: None,
            obligation_id: format!("test-{i:04x}"),
            site_key: format!("site-{i:04x}"),
            group_key: format!("grp-{:04x}", i / 4),
            id_build_local: false,
        };
        for i in 0..(ADVISORY_PER_CLASS_CAP as u32 + 25) {
            r.advisories.push(mk(i));
        }
        let html = render_html(&r, "many");
        assert!(
            html.contains("unproven obligation(s) to prove/guard"),
            "tally line kept"
        );
        assert!(
            html.contains("more unproven-obligation"),
            "boilerplate collapsed with a 'and N more' line"
        );
        // The capped HTML must NOT inline all of them.
        let shown = html.matches("PROVE/GUARD").count();
        assert!(
            shown <= ADVISORY_PER_CLASS_CAP,
            "at most the cap of non-fault rows inlined, got {shown}"
        );
        // …but the JSON feed carries the full set.
        let json = render_guidance_json(&r);
        let in_json = json.matches("\"class\":\"unproven-obligation\"").count();
        assert_eq!(
            in_json,
            ADVISORY_PER_CLASS_CAP + 25,
            "JSON feed carries every advisory"
        );
    }

    #[test]
    fn existing_panels_still_render() {
        // Regression: the redesign is additive — the core panels must survive.
        let r = analyze_wat(
            "(module (func $compute (export \"run\") (result i32) call $helper i32.const 7) \
             (func $helper nop))",
        );
        let html = render_html(&r, "panels");
        for needle in [
            "Summary",
            "Functions",
            "Call graph",
            "Diagnostics",
            "Program points",
            "Guidance — how to improve this code",
            "Trap checks",
        ] {
            assert!(html.contains(needle), "panel missing: {needle}");
        }
        assert!(html.starts_with("<!DOCTYPE html>"));
        assert!(html.ends_with("</html>"));
    }

    /// Minimal structural JSON validator: braces/brackets balance and string
    /// quotes are balanced (respecting `\"` escapes). Enough to catch a
    /// hand-rolled-emitter mistake without pulling in a JSON parser dep.
    fn assert_json_balanced(json: &str) {
        let mut depth: i32 = 0;
        let mut in_str = false;
        let mut escaped = false;
        for c in json.chars() {
            if in_str {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    in_str = false;
                }
                continue;
            }
            match c {
                '"' => in_str = true,
                '{' | '[' => depth += 1,
                '}' | ']' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "unbalanced closer in JSON");
        }
        assert_eq!(depth, 0, "unbalanced braces/brackets in JSON");
        assert!(!in_str, "unterminated string in JSON");
    }

    // ── FEAT-068 / FEAT-072 ─────────────────────────────────────────────

    /// One `i32.div_s` on an unknown divisor — the smallest fixture that
    /// raises a real, identity-stamped obligation.
    const DIV_A: &str = "(module (func (export \"a\") (param i32) (result i32) \
                         i32.const 10 local.get 0 i32.div_s))";

    #[test]
    fn feat068_guidance_json_carries_a_schema_version_and_the_identity_keys() {
        let r = analyze_wat(DIV_A);
        assert!(!r.advisories.is_empty(), "fixture must raise an advisory");
        // Non-vacuity: the analyzer must actually have stamped an id, else the
        // feed could carry three empty strings and still "contain" the keys.
        assert!(
            r.advisories.iter().any(|a| !a.obligation_id.is_empty()),
            "FEAT-064 must stamp an obligation_id"
        );
        assert!(
            r.advisories.iter().any(|a| !a.site_key.is_empty()),
            "site_key must be stamped"
        );
        let json = render_guidance_json(&r);
        assert!(
            json.contains("\"guidance_schema\":3"),
            "v2 feed must declare its version"
        );
        for k in ["obligation_id", "site_key", "group_key"] {
            assert!(json.contains(&format!("\"{k}\":\"")), "feed must carry {k}");
        }
        // And the values must be the real ones, not placeholders.
        let a = r
            .advisories
            .iter()
            .find(|a| !a.obligation_id.is_empty())
            .unwrap();
        assert!(
            json.contains(&format!("\"obligation_id\":\"{}\"", a.obligation_id)),
            "the feed's id must be the analyzer's id"
        );
    }

    #[test]
    fn feat072_advisory_rows_are_addressable_by_stable_id() {
        let r = analyze_wat(DIV_A);
        let a = r
            .advisories
            .iter()
            .find(|a| !a.obligation_id.is_empty())
            .expect("an identity-stamped advisory");
        let html = render_html(&r, "anchors");
        assert!(
            html.contains(&format!("id=\"ob-{}\"", a.obligation_id)),
            "every identified obligation must be an anchor target"
        );
        assert!(
            html.contains(&format!("href=\"#ob-{}\"", a.obligation_id)),
            "and must carry its own permalink"
        );
    }

    /// FEAT-072 AC: the citable URL must survive an edit in a DIFFERENT
    /// function — otherwise the anchor is no better than the `fn:pc` it
    /// replaces.
    #[test]
    fn feat072_anchor_survives_an_edit_in_an_unrelated_function() {
        let before = analyze_wat(
            "(module \
             (func (export \"a\") (param i32) (result i32) i32.const 10 local.get 0 i32.div_s) \
             (func (export \"b\") (param i32) (result i32) local.get 0))",
        );
        let after = analyze_wat(
            "(module \
             (func (export \"a\") (param i32) (result i32) i32.const 10 local.get 0 i32.div_s) \
             (func (export \"b\") (param i32) (result i32) local.get 0 i32.const 1 i32.add \
             local.get 0 i32.add))",
        );
        // Non-vacuity: the edit must actually have changed the module.
        assert_ne!(
            before.invariants.module_sha256, after.invariants.module_sha256,
            "the two fixtures must really differ, or this test proves nothing"
        );
        let id = before
            .advisories
            .iter()
            .find(|a| a.func_index == 0 && !a.obligation_id.is_empty())
            .map(|a| a.obligation_id.clone())
            .expect("fn a raises an identified obligation");
        let frag = format!("id=\"ob-{id}\"");
        assert!(render_html(&before, "before").contains(&frag));
        assert!(
            render_html(&after, "after").contains(&frag),
            "a link handed out before the edit must still resolve after it"
        );
    }

    /// The delta's own vacuity check: comparing a module with ITSELF must
    /// report nothing changed. A delta that "found changes" here would make
    /// every later number meaningless.
    #[test]
    fn feat072_delta_of_a_module_with_itself_reports_no_change() {
        let r = analyze_wat(DIV_A);
        let d = compute_delta(&r, &r);
        assert!(
            d.sites_before() > 0,
            "fixture must produce sites to compare"
        );
        assert_eq!(d.changed(), 0, "self-comparison must show no change");
        assert_eq!(d.only_before(), 0, "self-comparison loses no site");
        assert_eq!(d.only_after(), 0, "self-comparison gains no site");
        assert_eq!(d.unchanged(), d.sites_before(), "every site unchanged");
        assert_eq!(d.ordinal_stable_changes(), 0);
    }

    /// The DUAL check — without it, "no changes" could silently be the result
    /// of a broken match rather than of two equivalent modules.
    #[test]
    fn feat072_delta_of_known_different_modules_is_non_empty() {
        // Same site, but the divisor is now a non-zero constant, so the
        // div-by-zero obligation is discharged into a proven-safe fact.
        let before = analyze_wat(DIV_A);
        let after = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) \
             i32.const 10 i32.const 2 i32.div_s))",
        );
        assert_ne!(
            before.invariants.module_sha256, after.invariants.module_sha256,
            "fixtures must differ"
        );
        let d = compute_delta(&before, &after);
        assert!(
            d.changed() > 0 || d.only_before() > 0 || d.only_after() > 0,
            "a real edit must show up somewhere in the delta; got {d:?}"
        );
    }

    /// The soundness carve-out. Aliasing needs a same-kind SIBLING in the same
    /// ordinal domain (`ObligationId.v: survivor_inherits_deleted_identity`),
    /// so a singleton domain is provably alias-free and a populated one is not.
    #[test]
    fn feat072_ordinal_stable_requires_a_singleton_domain() {
        let one = analyze_wat(DIV_A);
        let d1 = compute_delta(&one, &one);
        assert!(
            d1.ordinal_stable() > 0,
            "a lone div_s has no same-kind sibling, so it is ordinal-stable"
        );
        assert_eq!(
            d1.not_excluded(),
            0,
            "…and nothing in that module should be flagged"
        );

        // Two same-kind operators in one region share an ordinal domain, so a
        // deletion could shift ordinals within it.
        let two = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) \
             i32.const 10 local.get 0 i32.div_s local.get 0 i32.div_s))",
        );
        let d2 = compute_delta(&two, &two);
        assert!(
            d2.not_excluded() > 0,
            "two same-kind sites must NOT be reported ordinal-stable"
        );
        assert_eq!(
            d2.ordinal_stable(),
            0,
            "no site in a populated domain may be reported ordinal-stable"
        );
    }

    /// The page's own arithmetic must add up. This caught a real defect: the
    /// moved-sites table filtered on `changed()` (true for gone and new rows
    /// too) while the summary counted in-place changes only, so a page could
    /// announce "7633 changed" above a summary saying "0 changed". Conflating
    /// vanished / new / changed is exactly how a delta misleads.
    #[test]
    fn feat072_moved_rows_reconcile_with_the_summary_counts() {
        let before = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) \
             i32.const 10 local.get 0 i32.div_s) \
             (func (export \"b\") (param i32) (result i32) \
             i32.const 7 local.get 0 i32.div_s))",
        );
        // `b` is gone entirely, and `a`'s divisor becomes a non-zero constant.
        let after = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) \
             i32.const 10 i32.const 2 i32.div_s))",
        );
        let d = compute_delta(&before, &after);
        let moved = d.rows.iter().filter(|r| r.changed()).count();
        assert_eq!(
            moved,
            d.only_before() + d.only_after() + d.changed(),
            "every moved row must be exactly one of gone / new / changed-in-place"
        );
        // Non-vacuity: this fixture must actually move something, or the
        // identity above holds trivially at 0 == 0.
        assert!(moved > 0, "the fixture must move at least one site");
        // And the three buckets must be disjoint by construction.
        for r in d.rows.iter().filter(|r| r.changed()) {
            let gone = !r.codes_before.is_empty() && r.codes_after.is_empty();
            let new = r.codes_before.is_empty() && !r.codes_after.is_empty();
            let inplace = r.in_both();
            assert_eq!(
                u8::from(gone) + u8::from(new) + u8::from(inplace),
                1,
                "a moved row must fall in exactly one bucket: {r:?}"
            );
        }
    }

    /// The limitation `OrdinalStable` does NOT cover, pinned so it cannot be
    /// forgotten or silently "fixed" without updating the page's disclosure.
    ///
    /// `group_key` hashes the region PATH, and a path is a sibling index at its
    /// depth. Delete a whole region and its later siblings renumber, so a
    /// surviving region moves into the deleted one's path and its sole operator
    /// inherits the entire key — while BOTH domains stay singletons and the
    /// ordinal check therefore sees nothing.
    ///
    /// Here the unsafe `div_s` is deleted along with its block, and the
    /// proven-safe `div_s` from the next block takes its identity. From the
    /// keys alone that is indistinguishable from the obligation being fixed.
    /// This is `survivor_inherits_deleted_identity` one level up the key.
    #[test]
    fn feat072_region_shift_is_not_certified_as_identity_held() {
        let before = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) (local i32) \
             (block i32.const 10 local.get 0 i32.div_s local.set 1) \
             (block i32.const 10 i32.const 2 i32.div_s local.set 1) \
             local.get 1))",
        );
        // The FIRST block — the one carrying the unproven obligation — is gone.
        let after = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) (local i32) \
             (block i32.const 10 i32.const 2 i32.div_s local.set 1) \
             local.get 1))",
        );
        let d = compute_delta(&before, &after);

        // CHARACTERIZATION, not an endorsement: the ordinal check cannot see a
        // region-path shift, so the survivor IS reported ordinal-stable and the
        // change IS counted. Pinned deliberately. If a future change makes this
        // 0, that is an improvement — and this test must fail so that the
        // page's disclosure is updated in the same commit rather than left
        // warning about a hazard that no longer exists.
        assert_eq!(
            d.ordinal_stable_changes(),
            1,
            "known limitation: a region-path shift is invisible to the ordinal check"
        );

        // What MUST hold: the page has to disclose it. A number the reader
        // cannot calibrate is worse than no number.
        let html = render_delta_html(&d, "region shift").to_lowercase();
        assert!(
            html.contains("region"),
            "the page must disclose the region-path hazard"
        );
        assert!(
            html.contains("not a certificate") || html.contains("not certif"),
            "the page must say plainly that ordinal-stable is not a certificate"
        );
    }

    /// DD-022, enforced mechanically: the published page must not make a
    /// verdict claim while scry#122 is open. Checked by grepping the rendered
    /// output, not by reviewer discipline.
    #[test]
    fn feat072_delta_page_makes_no_verdict_claim() {
        let before = analyze_wat(DIV_A);
        let after = analyze_wat(
            "(module (func (export \"a\") (param i32) (result i32) \
             i32.const 10 i32.const 2 i32.div_s))",
        );
        let html = render_delta_html(&compute_delta(&before, &after), "delta");
        let lower = html.to_lowercase();
        for banned in ["discharg", "verified fix", "obligation closed"] {
            assert!(
                !lower.contains(banned),
                "the delta page must not claim {banned:?} while scry#122 is open"
            );
        }
        // It must instead say what it DOES claim, and cite the refutation.
        assert!(
            lower.contains("alias-free"),
            "the honest headline must appear"
        );
        assert!(
            lower.contains("scry#122"),
            "the page must cite the refutation"
        );
        // The machine feed must be equally explicit.
        let json = render_delta_json(&compute_delta(&before, &after));
        assert!(json.contains("\"adjudicated\":false"));
        assert!(!json.to_lowercase().contains("discharg"));
    }

    // ── FEAT-076 (scry#123): surfacing build-local identity ─────────────────

    /// A module reaching BOTH identity tiers: two monomorphizations sharing a
    /// stripped name (→ build-local) and one unique stripped name (→ stable).
    fn mixed_tier_result() -> AnalysisResult {
        let r = analyze_wat(
            "(module \
               (func $\"_ZN3dep7generic17haaaaaaaaaaaaaaaaE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_ZN3dep7generic17hbbbbbbbbbbbbbbbbE\" (param i32) (result i32) \
                 i32.const 10 local.get 0 i32.div_s) \
               (func $\"_ZN4demo6unique17hccccccccccccccccE\" (param i32) (result i32) \
                 i32.const 30 local.get 0 i32.div_s))",
        );
        // Preconditions (anti-vacuity): the fixture must actually reach both
        // tiers, or every assertion downstream passes without testing anything.
        assert!(
            r.advisories
                .iter()
                .any(|a| !a.obligation_id.is_empty() && a.id_build_local),
            "fixture must produce a build-local identity; got {:?}",
            r.advisories
        );
        assert!(
            r.advisories
                .iter()
                .any(|a| !a.obligation_id.is_empty() && !a.id_build_local),
            "fixture must produce a stable identity; got {:?}",
            r.advisories
        );
        r
    }

    /// FEAT-076: the guidance feed must let a consumer tell a stable id from a
    /// build-local one WITHOUT parsing the id — and the schema version must
    /// say the field exists (FEAT-068: absence of a field from an old producer
    /// must be distinguishable).
    #[test]
    fn guidance_json_carries_id_build_local_and_v3_schema() {
        let r = mixed_tier_result();
        let json = render_guidance_json(&r);
        assert!(
            json.contains("\"guidance_schema\":3"),
            "id_build_local is a new field — the schema version must be bumped"
        );
        assert!(
            json.contains("\"id_build_local\":true"),
            "the ambiguous tier must be marked in the feed"
        );
        assert!(
            json.contains("\"id_build_local\":false"),
            "the stable tier must be explicitly unmarked in the feed"
        );
    }

    /// FEAT-076: the HTML guidance row must disclose a build-local id visibly,
    /// and must NOT stamp the disclosure on stable ids.
    #[test]
    fn guidance_html_marks_build_local_ids_only() {
        let html = render_html(&mixed_tier_result(), "bl");
        assert!(
            html.contains("build-local"),
            "a build-local id must be visibly marked in the HTML"
        );
        let stable = analyze_wat(
            "(module (func $compute (param i32) (result i32) \
               i32.const 10 local.get 0 i32.div_s))",
        );
        assert!(
            stable
                .advisories
                .iter()
                .any(|a| !a.obligation_id.is_empty() && !a.id_build_local),
            "precondition: stable fixture must produce a stable identity"
        );
        let html = render_html(&stable, "stable");
        assert!(
            !html.contains("build-local"),
            "a stable id must NOT carry the build-local marking"
        );
    }

    /// FEAT-076: the delta view compares runs BY identity, so it is exactly
    /// where a build-local id would be misread — a churned raw name shows up
    /// as one site vanishing and an unrelated one appearing. The row and the
    /// summaries must carry the flag, and the page must disclose it.
    #[test]
    fn delta_carries_build_local() {
        let r = mixed_tier_result();
        let d = compute_delta(&r, &r);
        assert!(
            d.rows.iter().any(|row| row.build_local),
            "a build-local site must be flagged in the delta rows"
        );
        assert!(
            d.rows.iter().any(|row| !row.build_local),
            "a stable site must not be flagged"
        );
        assert!(d.build_local_sites() >= 1, "summary count must see it");
        let json = render_delta_json(&d);
        assert!(
            json.contains("\"build_local_sites\":"),
            "delta JSON must carry the build-local count"
        );
        let html = render_delta_html(&d, "t").to_lowercase();
        assert!(
            html.contains("build-local"),
            "the delta page must disclose that some identities are build-local"
        );
    }
}

// ── FEAT-072: the delta view ────────────────────────────────────────────────
//
// The dashboard renders ONE snapshot, but the whole value of a stable
// obligation identity (FEAT-064) is ACROSS TIME. This module compares two
// analyses by identity rather than by position.
//
// WHAT IT DELIBERATELY DOES NOT DO: adjudicate. It reports no `discharged`
// count and draws no conclusion about whether a fix worked. Matching on a
// positional ordinal was refuted in review (scry#122) — a deletion paired with
// a same-kind insertion leaves a group's site set byte-identical, so "the
// group is unchanged" does NOT imply "identity did not alias".
//
// WHAT IT CAN SAY SOUNDLY. `ObligationId.v` proves aliasing via
// `survivor_inherits_deleted_identity`: a surviving site inherits a DELETED
// SIBLING's ordinal. That requires a sibling *in the same ordinal domain*.
// A domain (`group_key`) holding exactly one site in both runs therefore has
// no sibling to inherit from, and identity there provably cannot have aliased.
// That is a real, checkable carve-out, and it is the honest headline: not "K
// adjudicable" but "K provably alias-free, the rest not excluded".

/// FEAT-072: whether an obligation's identity could have aliased between two
/// runs — the only soundness claim the delta view makes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AliasStatus {
    /// The site's ordinal domain (`group_key`) holds exactly ONE site in both
    /// runs, so no same-kind SIBLING could have donated its ordinal
    /// (`ObligationId.v: survivor_inherits_deleted_identity` needs one).
    ///
    /// SCOPE — this rules out ORDINAL donation only. It does NOT certify that
    /// identity held. `group_key` hashes the region PATH, and a path is a
    /// sibling ordinal at its depth: deleting a whole region renumbers its
    /// later siblings, so a surviving region can occupy the deleted region's
    /// path and its sole operator inherits the whole key while both domains
    /// stay singletons. Demonstrated by
    /// `feat072_region_shift_is_not_certified_as_identity_held`.
    ///
    /// This variant was called `AliasFree` in drafting. The name was wrong:
    /// it reasoned from the one theorem that was proven rather than from what
    /// aliasing is, and a proof of one sufficient condition does not enumerate
    /// them. Renamed before publication.
    OrdinalStable,
    /// The domain holds two or more sites in one or both runs, so a deletion
    /// could have shifted ordinals within it. NOT a claim that aliasing
    /// happened — a claim that it is not excluded, which is the honest default.
    NotExcluded,
}

/// FEAT-072: one site's fate across two analyses, keyed on `site_key` (stable
/// across a code/class change) rather than on `(func_index, pc)`.
#[derive(Clone, Debug)]
pub struct DeltaRow {
    pub site_key: String,
    pub group_key: String,
    /// Advisory codes at this site in each run. A SET, not a scalar: one
    /// operator can raise several obligations (an `i32.div_s` raises both
    /// div-by-zero and signed-overflow), and `site_key` excludes the code, so
    /// they share a site. Modelling it as a set surfaces that multiplicity
    /// rather than silently picking one.
    pub codes_before: Vec<String>,
    pub codes_after: Vec<String>,
    pub func_index: u32,
    pub pc_before: Option<u32>,
    pub pc_after: Option<u32>,
    pub alias: AliasStatus,
    /// FEAT-076 (scry#123): TRUE when any advisory at this site, in either
    /// run, carries a BUILD-LOCAL identity (`Advisory::id_build_local`) — the
    /// site's keys are unique within one analysis but NOT comparable across
    /// builds, so its appearance/disappearance here is NOT evidence a site
    /// came or went: a churned raw name presents exactly the same way.
    pub build_local: bool,
}

impl DeltaRow {
    /// Present in both runs.
    pub fn in_both(&self) -> bool {
        !self.codes_before.is_empty() && !self.codes_after.is_empty()
    }
    /// The set of obligations at this site differs between the runs. NOTE: this
    /// is an OBSERVATION about the two reports, never a verdict about a fix.
    pub fn changed(&self) -> bool {
        self.codes_before != self.codes_after
    }
}

/// FEAT-072: the computed delta between two analyses.
#[derive(Clone, Debug, Default)]
pub struct Delta {
    pub rows: Vec<DeltaRow>,
    pub sha_before: String,
    pub sha_after: String,
}

impl Delta {
    pub fn sites_before(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| !r.codes_before.is_empty())
            .count()
    }
    pub fn sites_after(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| !r.codes_after.is_empty())
            .count()
    }
    pub fn only_before(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| !r.codes_before.is_empty() && r.codes_after.is_empty())
            .count()
    }
    pub fn only_after(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.codes_before.is_empty() && !r.codes_after.is_empty())
            .count()
    }
    pub fn changed(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.in_both() && r.changed())
            .count()
    }
    pub fn unchanged(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.in_both() && !r.changed())
            .count()
    }
    /// Sites present in both runs whose identity provably did not alias.
    pub fn ordinal_stable(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.in_both() && r.alias == AliasStatus::OrdinalStable)
            .count()
    }
    /// Sites present in both runs where aliasing is not excluded.
    pub fn not_excluded(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.in_both() && r.alias == AliasStatus::NotExcluded)
            .count()
    }
    /// FEAT-076 (scry#123): sites whose identity is BUILD-LOCAL in at least
    /// one run — rows on which cross-build comparison is not meaningful.
    pub fn build_local_sites(&self) -> usize {
        self.rows.iter().filter(|r| r.build_local).count()
    }
    /// The rows a future adjudicator (REQ-021) could act on soundly TODAY:
    /// present in both runs, obligation set changed, and provably alias-free.
    /// Reported as a COUNT OF CANDIDATES, never as discharges.
    pub fn ordinal_stable_changes(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.in_both() && r.changed() && r.alias == AliasStatus::OrdinalStable)
            .count()
    }
}

/// FEAT-072: compare two analyses by stable identity.
///
/// Both inputs must come from the same producer version — `site_key` is a hash
/// over a key tuple whose derivation is not a cross-version contract.
pub fn compute_delta(before: &AnalysisResult, after: &AnalysisResult) -> Delta {
    use std::collections::{BTreeMap, BTreeSet};

    // group_key -> the set of distinct sites in that ordinal domain, per run.
    fn groups(r: &AnalysisResult) -> BTreeMap<&str, BTreeSet<&str>> {
        let mut m: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for a in r.advisories.iter().filter(|a| !a.site_key.is_empty()) {
            m.entry(a.group_key.as_str())
                .or_default()
                .insert(a.site_key.as_str());
        }
        m
    }
    // site_key -> (group_key, func_index, pc, sorted distinct codes,
    //              any advisory here build-local (FEAT-076))
    #[allow(clippy::type_complexity)]
    fn sites(r: &AnalysisResult) -> BTreeMap<&str, (&str, u32, u32, BTreeSet<&str>, bool)> {
        let mut m: BTreeMap<&str, (&str, u32, u32, BTreeSet<&str>, bool)> = BTreeMap::new();
        for a in r.advisories.iter().filter(|a| !a.site_key.is_empty()) {
            let e = m.entry(a.site_key.as_str()).or_insert((
                a.group_key.as_str(),
                a.func_index,
                a.pc,
                BTreeSet::new(),
                false,
            ));
            e.3.insert(a.code.as_str());
            e.4 |= a.id_build_local;
        }
        m
    }

    let (gb, ga) = (groups(before), groups(after));
    let (sb, sa) = (sites(before), sites(after));

    let mut keys: BTreeSet<&str> = BTreeSet::new();
    keys.extend(sb.keys().copied());
    keys.extend(sa.keys().copied());

    let mut rows = Vec::with_capacity(keys.len());
    for k in keys {
        let b = sb.get(k);
        let a = sa.get(k);
        let group = b.map(|x| x.0).or_else(|| a.map(|x| x.0)).unwrap_or("");
        // Alias-free ONLY when the ordinal domain is a singleton in BOTH runs:
        // with no sibling there is nothing for a survivor to inherit from.
        // A domain absent from one run cannot be certified, so `is_some_and`
        // (false when absent) is the correct conservative default — a vacuous
        // `true` here would certify exactly the sites we know least about.
        let alias = if gb.get(group).is_some_and(|s| s.len() == 1)
            && ga.get(group).is_some_and(|s| s.len() == 1)
        {
            AliasStatus::OrdinalStable
        } else {
            AliasStatus::NotExcluded
        };
        rows.push(DeltaRow {
            site_key: k.to_string(),
            group_key: group.to_string(),
            codes_before: b
                .map(|x| x.3.iter().map(|s| s.to_string()).collect())
                .unwrap_or_default(),
            codes_after: a
                .map(|x| x.3.iter().map(|s| s.to_string()).collect())
                .unwrap_or_default(),
            func_index: b.map(|x| x.1).or_else(|| a.map(|x| x.1)).unwrap_or(0),
            pc_before: b.map(|x| x.2),
            pc_after: a.map(|x| x.2),
            alias,
            // FEAT-076: build-local in EITHER run poisons cross-run
            // comparability of the row, so either flag marks it.
            build_local: b.map(|x| x.4).unwrap_or(false) || a.map(|x| x.4).unwrap_or(false),
        });
    }

    Delta {
        rows,
        sha_before: before.invariants.module_sha256.clone(),
        sha_after: after.invariants.module_sha256.clone(),
    }
}

/// FEAT-072: render a [`Delta`] as a self-contained page.
///
/// HONESTY CONSTRAINT (DD-022, enforced by `delta_page_makes_no_discharge_claim`):
/// this page contains NO discharge count and no verdict vocabulary. Its
/// headline is the alias-free fraction, because that is the one figure the
/// scry#122 refutation did not undermine and because it states exactly how far
/// a future adjudicator (REQ-021) could be trusted on this pair. When REQ-021
/// lands, verdicts are ADDED here — the framing above does not have to be
/// walked back.
pub fn render_delta_html(d: &Delta, title: &str) -> String {
    let mut s = String::with_capacity(8 * 1024);
    let _ = write!(s, "{}", DOCTYPE_AND_HEAD_OPEN);
    let _ = write!(s, "<title>{} — {}</title>", esc(HERO_TITLE), esc(title));
    let _ = write!(s, "{}", STYLE);
    s.push_str("</head><body>");
    let _ = write!(s, "<h1>{} — {}</h1>", esc(HERO_TITLE), esc(title));

    // What this page is, and — more importantly — what it is not.
    s.push_str(
        "<section><h2>What this page claims</h2>\
         <p>This is a comparison of two analyses <strong>by stable obligation \
         identity</strong> (FEAT-064), not by <code>(func_index, pc)</code>. \
         It reports what <em>changed</em>. It does <strong>not</strong> report \
         that anything was proved.</p>\
         <p>Adjudication — turning an observed change into a <em>verdict</em> — \
         is deliberately absent. Matching obligations on a positional ordinal \
         was refuted in review (<code>scry#122</code>): a deletion paired with a \
         same-kind insertion leaves an ordinal domain's site set byte-identical, \
         so an unchanged domain does <em>not</em> imply identity held. An \
         adjudicator that can wrongly report success is worse than none, \
         because the cheapest way to satisfy it is to delete the code.</p>\
         <p>The one claim made here is narrow and its name says so: \
         <strong>ordinal-stable</strong>. A site whose ordinal domain holds \
         exactly one member in <em>both</em> runs cannot have had its ordinal \
         donated by a same-kind sibling, because \
         <code>ObligationId.v: survivor_inherits_deleted_identity</code> needs \
         one and a singleton domain has none.</p>\
         <p><strong>That is not a certificate that identity held.</strong> The \
         key hashes a region <em>path</em>, and a path is a sibling index at \
         its depth — so deleting a whole region renumbers its later siblings, \
         and a surviving region can move into the deleted one's path. Its sole \
         operator then inherits the entire key while both domains remain \
         singletons. An obligation removed by deleting its region can therefore \
         look, from the keys alone, exactly like one that changed state. This \
         page reports what moved; establishing that a change belongs to a \
         particular site needs corroboration these keys do not carry \
         (<code>scry#122</code>, <code>scry#123</code>).</p>\
         <p>Everything not ordinal-stable is <strong>not excluded</strong> — a \
         statement about our knowledge, not about the code.</p></section>",
    );

    let both = d.ordinal_stable() + d.not_excluded();
    let pct = if both == 0 {
        0.0
    } else {
        100.0 * d.ordinal_stable() as f64 / both as f64
    };
    s.push_str("<section><h2>Summary</h2><dl>");
    let _ = write!(
        s,
        "<dt>module before</dt><dd><code>{}</code></dd>\
         <dt>module after</dt><dd><code>{}</code></dd>\
         <dt>sites before / after</dt><dd>{} / {}</dd>\
         <dt class=\"warn\">…with a build-local identity</dt><dd class=\"warn\">{}</dd>\
         <dt>present in both</dt><dd>{}</dd>\
         <dt class=\"ok\">…ordinal-stable</dt><dd class=\"ok\">{} ({:.1}%)</dd>\
         <dt class=\"warn\">…ordinal donation not excluded</dt><dd class=\"warn\">{}</dd>\
         <dt>only in before (site gone)</dt><dd>{}</dd>\
         <dt>only in after (site new)</dt><dd>{}</dd>\
         <dt>obligation set changed</dt><dd>{}</dd>\
         <dt>…of those, ordinal-stable</dt><dd>{}</dd>",
        esc(&d.sha_before),
        esc(&d.sha_after),
        d.sites_before(),
        d.sites_after(),
        d.build_local_sites(),
        both,
        d.ordinal_stable(),
        pct,
        d.not_excluded(),
        d.only_before(),
        d.only_after(),
        d.changed(),
        d.ordinal_stable_changes(),
    );
    s.push_str("</dl>");
    s.push_str(
        "<p class=\"muted\">The <em>ordinal-stable</em> subtotal is the rows on \
         which one specific hazard — a same-kind sibling donating its ordinal — \
         is excluded. It is a filter, not a warrant: a region-path shift can \
         still move a key between operators, so these are the rows worth \
         looking at FIRST, not the rows that are settled.</p>",
    );
    s.push_str(
        "<p class=\"muted\">A site \"only in before\" is <strong>not</strong> a \
         fix: the code that carried the obligation may simply be gone, which \
         proves nothing.</p>",
    );
    // FEAT-076 (scry#123): rows whose identity is build-local are hashed from
    // a raw disambiguated name that churns across builds — their appearance
    // or disappearance between two builds is expected noise, not evidence.
    s.push_str(
        "<p class=\"muted\">A <strong>build-local</strong> identity (the count \
         above) is unique within one build only: the function's stripped name \
         is shared (dependency generics), so the raw name — which carries a \
         crate-metadata disambiguator and churns across builds — is hashed. \
         Such a site vanishing or appearing between builds is expected \
         identity churn, not evidence a site came or went (scry#123).\
         </p></section>",
    );

    // Only rows that MOVED. An unchanged row carries no information, and the
    // whole point of a delta is that it is small.
    //
    // The `fate` column exists because "changed" is three different events and
    // conflating them is how a delta misleads: a site that VANISHED is not a
    // site that changed class, and neither is a fix. The summary above counts
    // in-place changes only; this table shows all three and says which is which.
    s.push_str("<section><h2>Sites that moved</h2>");
    let moved: Vec<&DeltaRow> = d.rows.iter().filter(|r| r.changed()).collect();
    let shown: Vec<&&DeltaRow> = moved.iter().take(SECTION_ROW_CAP).collect();
    if moved.is_empty() {
        s.push_str(
            "<p class=\"empty\">No site moved. If the two modules differ, that is \
             itself worth investigating — see the self-comparison and \
             known-different controls in the test suite.</p>",
        );
    } else {
        let _ = write!(
            s,
            "<p><strong>{}</strong> site(s) moved — {} gone, {} new, \
             {} changed in place{}.</p>\
             <table><tr><th>site</th><th>fn:pc</th><th>fate</th><th>alias</th>\
             <th>before</th><th>after</th></tr>",
            moved.len(),
            d.only_before(),
            d.only_after(),
            d.changed(),
            if moved.len() > shown.len() {
                format!(" — showing the first {}", shown.len())
            } else {
                String::new()
            },
        );
        for r in shown {
            let (fcls, ftxt) = match (r.codes_before.is_empty(), r.codes_after.is_empty()) {
                (true, false) => ("info", "new"),
                (false, true) => ("muted", "gone"),
                _ => ("warn", "changed"),
            };
            let (acls, atxt) = match r.alias {
                AliasStatus::OrdinalStable => ("ok", "alias-free"),
                AliasStatus::NotExcluded => ("warn", "not excluded"),
            };
            let pcs = match (r.pc_before, r.pc_after) {
                (Some(b), Some(a)) if b == a => format!("fn{}:{}", r.func_index, b),
                (Some(b), Some(a)) => format!("fn{}:{}→{}", r.func_index, b, a),
                (Some(b), None) => format!("fn{}:{}", r.func_index, b),
                (None, Some(a)) => format!("fn{}:{}", r.func_index, a),
                (None, None) => "—".to_string(),
            };
            let fmt = |v: &Vec<String>| {
                if v.is_empty() {
                    "<span class=\"muted\">—</span>".to_string()
                } else {
                    v.iter()
                        .map(|c| format!("<code>{}</code>", esc(c)))
                        .collect::<Vec<_>>()
                        .join(" ")
                }
            };
            let _ = write!(
                s,
                "<tr><td><code>{}</code></td><td><code>{}</code></td>\
                 <td class=\"{}\">{}</td><td class=\"{}\">{}</td>\
                 <td>{}</td><td>{}</td></tr>",
                esc(&r.site_key),
                esc(&pcs),
                fcls,
                ftxt,
                acls,
                atxt,
                fmt(&r.codes_before),
                fmt(&r.codes_after),
            );
        }
        s.push_str("</table>");
    }
    s.push_str("</section>");

    s.push_str(
        "<footer>Rendered by scry-viz · a comparison of two analyses by stable \
        identity. No verdict is asserted; see scry#122. MIT OR Apache-2.0.</footer>",
    );
    s.push_str("</body></html>");
    s
}

/// FEAT-072: the delta as a machine-consumable summary — what the FEAT-073
/// harness aggregates across a run of commits.
pub fn render_delta_json(d: &Delta) -> String {
    let mut s = String::with_capacity(1024);
    let _ = write!(
        s,
        "{{\"guidance_schema\":{},\"kind\":\"delta\",\
         \"adjudicated\":false,\"adjudication_issue\":\"scry#122\",\
         \"module_sha256_before\":\"{}\",\"module_sha256_after\":\"{}\",\
         \"sites_before\":{},\"sites_after\":{},\
         \"build_local_sites\":{},\
         \"ordinal_stable\":{},\"not_excluded\":{},\
         \"only_before\":{},\"only_after\":{},\
         \"changed\":{},\"unchanged\":{},\"ordinal_stable_changes\":{}}}",
        GUIDANCE_SCHEMA_VERSION,
        json_esc(&d.sha_before),
        json_esc(&d.sha_after),
        d.sites_before(),
        d.sites_after(),
        d.build_local_sites(),
        d.ordinal_stable(),
        d.not_excluded(),
        d.only_before(),
        d.only_after(),
        d.changed(),
        d.unchanged(),
        d.ordinal_stable_changes(),
    );
    s
}
