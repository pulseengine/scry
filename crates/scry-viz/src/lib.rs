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
    AbstractValue, AnalysisResult, CallEdge, Diagnostic, DiagnosticSeverity, FunctionStack,
    Interval, ProgramPoint, Region, SoundnessTag, StackBound,
};

/// Render a complete, self-contained HTML document for `result`.
///
/// `title` is shown in the page `<title>` and `<h1>` — typically the analyzed
/// module's name. The returned `String` is the entire document (UTF-8); write
/// it to a `.html` file and open it directly.
pub fn render_html(result: &AnalysisResult, title: &str) -> String {
    let mut s = String::with_capacity(8 * 1024);
    let _ = write!(s, "{}", DOCTYPE_AND_HEAD_OPEN);
    let _ = write!(s, "<title>scry-viz — {}</title>", esc(title));
    let _ = write!(s, "{}", STYLE);
    s.push_str("</head><body>");

    let _ = write!(s, "<h1>scry analysis — {}</h1>", esc(title));
    render_header(&mut s, result);
    render_functions(&mut s, result);
    render_call_graph(&mut s, &result.call_graph);
    render_diagnostics(&mut s, &result.diagnostics);
    render_points(&mut s, &result.invariants.points);

    s.push_str(
        "<footer>Rendered by scry-viz · a faithful projection of the \
        analyzer output (nothing re-derived). MIT OR Apache-2.0.</footer>",
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
    kv(s, "program points", &points.to_string());
    s.push_str("</dl></section>");
}

fn render_functions(s: &mut String, r: &AnalysisResult) {
    s.push_str("<section><h2>Functions</h2>");
    if r.function_summaries.is_empty() && r.stack_usage.functions.is_empty() {
        s.push_str("<p class=\"empty\">No functions.</p></section>");
        return;
    }
    s.push_str(
        "<table><thead><tr><th>func</th><th>reachable</th><th>recursive</th>\
         <th>params</th><th>frame</th><th>max stack</th></tr></thead><tbody>",
    );
    // Union of every function index we know something about, ascending.
    let mut indices: Vec<u32> = r
        .function_summaries
        .iter()
        .map(|f| f.func_index)
        .chain(r.stack_usage.functions.iter().map(|f| f.func_index))
        .collect();
    indices.sort_unstable();
    indices.dedup();
    for idx in indices {
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
        let _ = write!(
            s,
            "<tr><td>{idx}</td><td>{}</td><td>{}</td><td>{params}</td>\
             <td>{frame}</td><td>{maxs}</td></tr>",
            yesno(reachable),
            yesno(recursive),
        );
    }
    s.push_str("</tbody></table></section>");
}

fn render_call_graph(s: &mut String, edges: &[CallEdge]) {
    s.push_str("<section><h2>Call graph</h2>");
    if edges.is_empty() {
        s.push_str("<p class=\"empty\">No call edges.</p></section>");
        return;
    }
    s.push_str(
        "<table><thead><tr><th>caller</th><th>pc</th><th>kind</th>\
         <th>resolved targets</th><th>soundness</th></tr></thead><tbody>",
    );
    for e in edges {
        let targets = if e.resolved_targets.is_empty() {
            "(none)".to_string()
        } else {
            e.resolved_targets
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        };
        let sound = match e.soundness {
            SoundnessTag::Sound => "<span class=\"ok\">sound</span>",
            SoundnessTag::UnsoundFallback => "<span class=\"warn\">unsound-fallback</span>",
        };
        let _ = write!(
            s,
            "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{sound}</td></tr>",
            e.caller_func,
            e.pc,
            if e.indirect { "call_indirect" } else { "call" },
            esc(&targets),
        );
    }
    s.push_str("</tbody></table></section>");
}

fn render_diagnostics(s: &mut String, diags: &[Diagnostic]) {
    s.push_str("<section><h2>Diagnostics</h2>");
    if diags.is_empty() {
        s.push_str("<p class=\"empty\">No diagnostics.</p></section>");
        return;
    }
    s.push_str("<ul class=\"diags\">");
    for d in diags {
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
    s.push_str("</ul></section>");
}

fn render_points(s: &mut String, points: &[ProgramPoint]) {
    s.push_str("<section><h2>Program points</h2>");
    if points.is_empty() {
        s.push_str("<p class=\"empty\">No program points.</p></section>");
        return;
    }
    s.push_str(
        "<table><thead><tr><th>func</th><th>pc</th><th>locals</th>\
         <th>operand stack (bottom → top)</th></tr></thead><tbody>",
    );
    for p in points {
        let locals = if p.locals.is_empty() {
            "(none)".to_string()
        } else {
            p.locals
                .iter()
                .map(|l| format!("L{}={}", l.local_index, abstract_value(&l.value)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        // FEAT-023: the abstract operand stack. Empty is shown as "(empty)" —
        // the analyzer's honest "no operand-stack info here", not a claim that
        // the concrete stack is empty.
        let stack = if p.operand_stack.is_empty() {
            "<span class=\"empty\">(empty)</span>".to_string()
        } else {
            p.operand_stack
                .iter()
                .map(abstract_value)
                .collect::<Vec<_>>()
                .join(" · ")
        };
        let _ = write!(
            s,
            "<tr><td>{}</td><td>{}</td><td><code>{}</code></td>\
             <td><code>{}</code></td></tr>",
            p.func_index,
            p.pc,
            esc(&locals),
            stack,
        );
    }
    s.push_str("</tbody></table></section>");
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
    fn no_panic_on_empty_module() {
        let r = analyze_wat("(module)");
        let html = render_html(&r, "empty");
        assert!(html.contains("No functions.") || html.contains("Functions"));
        assert!(html.ends_with("</html>"));
    }
}
