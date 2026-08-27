//! scry-mcp — MCP server library (FEAT-066, REQ-017/REQ-020, TE-011).
//!
//! Exposes the scry sound abstract interpreter to AI agents over the Model
//! Context Protocol: JSON-RPC 2.0, newline-delimited, on stdio. Agents cannot
//! run `cargo`; before this crate, consuming scry meant shelling out to a CLI
//! or scraping a multi-MB JSON dump. The tool surface is deliberately
//! structured-primary (TE-011: agents under-read rendered output) — every
//! result is compact JSON, never HTML, never the full `AnalysisResult`.
//!
//! The JSON-RPC layer is HAND-ROLLED on `serde_json` by design: MCP's stdio
//! transport needs exactly three methods (`initialize`, `tools/list`,
//! `tools/call`) plus notification tolerance, and an MCP SDK dependency would
//! have to clear cargo-deny while buying nothing at this size.

use scry_analyze_core::{AdvisoryClass, AnalysisConfig, GapKind, Query, TrapVerdict, analyze};
use serde_json::{Map, Value, json};

/// The MCP protocol revision this server implements.
const PROTOCOL_VERSION: &str = "2025-06-18";

/// Cap on `query` matches returned in one response, overridable per call via
/// the `limit` argument. Keeps the worst case (an unconstrained query over a
/// large module) a bounded payload instead of a multi-MB dump (FEAT-066 AC#1);
/// `total_matches`/`truncated` always report what the cap hid.
const DEFAULT_QUERY_LIMIT: usize = 100;

/// The v3.3.0 tool surface: `analyze` and `query` ONLY.
///
/// `verify` is deliberately ABSENT, and its absence is enforced HERE — by the
/// tool list a client actually enumerates — not by documentation (FEAT-066
/// AC#2; same family as DD-022: a deferral a consumer can rely on must be
/// structural). Do NOT "helpfully" add it: FEAT-065's `verify_against` exists
/// and is `accepted`, but REQ-021 MEASURED that on real inputs `discharged`
/// is 0 and every verdict degrades to `uncertain` (the identity tier on
/// stripped release builds is the body-shape hash, which an edit changes by
/// construction — see `Advisory::ident_survives_own_edit`). Exposing that
/// over MCP would put an always-`uncertain` verdict directly into an agent's
/// tool loop, the single worst place for it to land. `verify` follows
/// FEAT-065 into v3.4.0 with REQ-021.
fn tool_definitions() -> Value {
    json!([
        {
            "name": "analyze",
            "description": "Run the scry sound abstract interpreter over a \
                Wasm module (.wasm binary or .wat text, by path) and return a \
                compact structured summary: advisory counts by actionability \
                class and code, runtime-trap verdicts (proven-safe vs \
                potential-trap), and precision-gap counts. Never HTML, never \
                a full dump — use the `query` tool to retrieve specific \
                advisory sites.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "module_path": {
                        "type": "string",
                        "description": "Path to the module to analyze \
                            (.wasm or .wat)."
                    }
                },
                "required": ["module_path"]
            }
        },
        {
            "name": "query",
            "description": "Filter the advisories of a Wasm module's scry \
                analysis (FEAT-067): every given filter is ANDed, an omitted \
                filter is unconstrained. Returns the matching advisory sites \
                with their stable obligation identities (REQ-020), capped by \
                `limit` with an exact `total_matches` count.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "module_path": {
                        "type": "string",
                        "description": "Path to the module to analyze \
                            (.wasm or .wat)."
                    },
                    "class": {
                        "type": "string",
                        "enum": ["definite-fault", "unproven-obligation",
                                 "precision-gap", "leverageable-fact"],
                        "description": "Advisory actionability class."
                    },
                    "code": {
                        "type": "string",
                        "description": "Advisory category code, e.g. \
                            `div-by-zero`, `use-after-drop`, `proven-safe`."
                    },
                    "func_index": {
                        "type": "integer",
                        "description": "Absolute function index."
                    },
                    "op": {
                        "type": "string",
                        "description": "Operator name in wasm text format \
                            (e.g. `i32.div_u`), joined from the gap / \
                            trap-check record at the same site."
                    },
                    "gap_kind": {
                        "type": "string",
                        "enum": ["unsupported-op", "unmodeled-branch",
                                 "unmodeled-memory-address",
                                 "unmodeled-control-flow"],
                        "description": "Gap kind, joined from the gap record \
                            at the same site."
                    },
                    "limit": {
                        "type": "integer",
                        "description": "Maximum matches to return \
                            (default 100); `total_matches` is always exact."
                    }
                },
                "required": ["module_path"]
            }
        }
    ])
}

/// Handle one newline-delimited JSON-RPC message. Returns the response line
/// to write, or `None` when the message is a notification (no `id`) — a
/// notification must never be answered, or the stdio stream corrupts.
pub fn handle_line(line: &str) -> Option<String> {
    let msg: Value = match serde_json::from_str(line) {
        Ok(v) => v,
        Err(e) => {
            return Some(
                error_response(Value::Null, -32700, &format!("parse error: {e}")).to_string(),
            );
        }
    };
    let id = msg.get("id").cloned();
    let method = msg.get("method").and_then(Value::as_str).unwrap_or("");
    let params = msg.get("params").cloned().unwrap_or(Value::Null);

    // Requests carry an id; anything without one is a notification
    // (e.g. `notifications/initialized`) and gets no response.
    let id = id?;

    let resp = match method {
        "initialize" => json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": {
                "protocolVersion": PROTOCOL_VERSION,
                "capabilities": { "tools": {} },
                "serverInfo": {
                    "name": "scry-mcp",
                    "version": env!("CARGO_PKG_VERSION")
                }
            }
        }),
        "ping" => json!({ "jsonrpc": "2.0", "id": id, "result": {} }),
        "tools/list" => json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": { "tools": tool_definitions() }
        }),
        "tools/call" => handle_tool_call(id, &params),
        other => error_response(id, -32601, &format!("method not found: {other}")),
    };
    Some(resp.to_string())
}

fn error_response(id: Value, code: i64, message: &str) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "error": { "code": code, "message": message }
    })
}

/// A tool EXECUTION failure (unreadable path, invalid module): reported
/// in-band as an `isError` result so the agent sees it as tool output it can
/// react to, per MCP — reserved JSON-RPC errors are for protocol misuse.
fn tool_error(id: Value, message: &str) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "result": {
            "content": [{ "type": "text", "text": message }],
            "isError": true
        }
    })
}

fn tool_result(id: Value, payload: &Value) -> Value {
    json!({
        "jsonrpc": "2.0",
        "id": id,
        "result": {
            "content": [{ "type": "text", "text": payload.to_string() }],
            "structuredContent": payload,
            "isError": false
        }
    })
}

fn handle_tool_call(id: Value, params: &Value) -> Value {
    let name = params.get("name").and_then(Value::as_str).unwrap_or("");
    let args = params.get("arguments").cloned().unwrap_or(json!({}));
    match name {
        "analyze" => run_analyze(id, &args),
        "query" => run_query(id, &args),
        // `verify` deliberately lands here too — see `tool_definitions`.
        other => error_response(id, -32602, &format!("unknown tool: {other}")),
    }
}

/// Load + analyze the module named by `arguments.module_path`. `Err(String)`
/// is a USER-INPUT problem (missing/invalid argument → the caller maps it to
/// -32602); `Err` inside the returned `Result`'s `Ok` path never happens —
/// I/O and analysis failures are returned as `Ok(Err(msg))` for in-band
/// reporting.
#[allow(clippy::type_complexity)]
fn load_and_analyze(
    args: &Value,
) -> Result<Result<scry_analyze_core::AnalysisResult, String>, String> {
    let path = args
        .get("module_path")
        .and_then(Value::as_str)
        .ok_or_else(|| "missing required argument: module_path (string)".to_string())?;
    let bytes = match wat::parse_file(path) {
        Ok(b) => b,
        Err(e) => return Ok(Err(format!("cannot load module `{path}`: {e}"))),
    };
    match analyze(bytes, AnalysisConfig::default()) {
        Ok(r) => Ok(Ok(r)),
        Err(e) => Ok(Err(format!("analysis of `{path}` failed: {e:?}"))),
    }
}

fn class_str(c: AdvisoryClass) -> &'static str {
    match c {
        AdvisoryClass::DefiniteFault => "definite-fault",
        AdvisoryClass::UnprovenObligation => "unproven-obligation",
        AdvisoryClass::PrecisionGap => "precision-gap",
        AdvisoryClass::LeverageableFact => "leverageable-fact",
    }
}

fn parse_class(s: &str) -> Option<AdvisoryClass> {
    match s {
        "definite-fault" => Some(AdvisoryClass::DefiniteFault),
        "unproven-obligation" => Some(AdvisoryClass::UnprovenObligation),
        "precision-gap" => Some(AdvisoryClass::PrecisionGap),
        "leverageable-fact" => Some(AdvisoryClass::LeverageableFact),
        _ => None,
    }
}

fn gap_kind_str(k: GapKind) -> &'static str {
    match k {
        GapKind::UnsupportedOp => "unsupported-op",
        GapKind::UnmodeledBranch => "unmodeled-branch",
        GapKind::UnmodeledMemoryAddress => "unmodeled-memory-address",
        GapKind::UnmodeledControlFlow => "unmodeled-control-flow",
    }
}

fn parse_gap_kind(s: &str) -> Option<GapKind> {
    match s {
        "unsupported-op" => Some(GapKind::UnsupportedOp),
        "unmodeled-branch" => Some(GapKind::UnmodeledBranch),
        "unmodeled-memory-address" => Some(GapKind::UnmodeledMemoryAddress),
        "unmodeled-control-flow" => Some(GapKind::UnmodeledControlFlow),
        _ => None,
    }
}

/// `analyze` tool: the AC#1 structured summary — counts by advisory class and
/// code, trap verdicts, gap counts. COUNTS, not sites: the per-site data is
/// what `query` is for, which is how the summary stays kilobytes on a module
/// whose full `AnalysisResult` serializes to multiple MB.
fn run_analyze(id: Value, args: &Value) -> Value {
    let r = match load_and_analyze(args) {
        Err(bad_args) => return error_response(id, -32602, &bad_args),
        Ok(Err(msg)) => return tool_error(id, &msg),
        Ok(Ok(r)) => r,
    };

    let mut by_class = Map::new();
    for c in [
        AdvisoryClass::DefiniteFault,
        AdvisoryClass::UnprovenObligation,
        AdvisoryClass::PrecisionGap,
        AdvisoryClass::LeverageableFact,
    ] {
        let n = r.advisories.iter().filter(|a| a.class == c).count();
        by_class.insert(class_str(c).to_string(), json!(n));
    }
    let mut by_code = Map::new();
    for a in &r.advisories {
        let e = by_code.entry(a.code.clone()).or_insert(json!(0));
        *e = json!(e.as_u64().unwrap_or(0) + 1);
    }
    let mut gaps_by_kind = Map::new();
    for g in &r.gaps {
        let e = gaps_by_kind
            .entry(gap_kind_str(g.kind).to_string())
            .or_insert(json!(0));
        *e = json!(e.as_u64().unwrap_or(0) + 1);
    }
    let n_potential = r
        .trap_checks
        .iter()
        .filter(|t| t.verdict == TrapVerdict::PotentialTrap)
        .count();
    let n_safe = r
        .trap_checks
        .iter()
        .filter(|t| t.verdict == TrapVerdict::ProvenSafe)
        .count();

    let payload = json!({
        "functions": r.function_summaries.len(),
        "advisories": {
            "total": r.advisories.len(),
            "by_class": by_class,
            "by_code": by_code
        },
        "trap_checks": {
            "total": r.trap_checks.len(),
            "proven-safe": n_safe,
            "potential-trap": n_potential
        },
        "gaps": {
            "total": r.gaps.len(),
            "by_kind": gaps_by_kind
        }
    });
    tool_result(id, &payload)
}

/// `query` tool: `AnalysisResult::query` (FEAT-067) over MCP — each filter
/// argument maps to the corresponding `Query` field, ANDed, `None` when
/// omitted.
fn run_query(id: Value, args: &Value) -> Value {
    let mut q = Query::default();
    if let Some(v) = args.get("class") {
        let Some(c) = v.as_str().and_then(parse_class) else {
            return error_response(
                id,
                -32602,
                &format!(
                    "invalid class {v}: expected one of definite-fault, \
                     unproven-obligation, precision-gap, leverageable-fact"
                ),
            );
        };
        q.class = Some(c);
    }
    if let Some(v) = args.get("gap_kind") {
        let Some(k) = v.as_str().and_then(parse_gap_kind) else {
            return error_response(
                id,
                -32602,
                &format!(
                    "invalid gap_kind {v}: expected one of unsupported-op, \
                     unmodeled-branch, unmodeled-memory-address, \
                     unmodeled-control-flow"
                ),
            );
        };
        q.gap_kind = Some(k);
    }
    q.code = args.get("code").and_then(Value::as_str).map(String::from);
    q.op = args.get("op").and_then(Value::as_str).map(String::from);
    q.func_index = args
        .get("func_index")
        .and_then(Value::as_u64)
        .map(|f| f as u32);
    let limit = args
        .get("limit")
        .and_then(Value::as_u64)
        .map(|l| l as usize)
        .unwrap_or(DEFAULT_QUERY_LIMIT);

    let r = match load_and_analyze(args) {
        Err(bad_args) => return error_response(id, -32602, &bad_args),
        Ok(Err(msg)) => return tool_error(id, &msg),
        Ok(Ok(r)) => r,
    };
    let matches = r.query(&q);
    let total = matches.len();
    let shown: Vec<Value> = matches
        .iter()
        .take(limit)
        .map(|a| {
            json!({
                "func_index": a.func_index,
                "pc": a.pc,
                "class": class_str(a.class),
                "code": a.code,
                "detail": a.detail,
                "suggested_action": a.suggested_action,
                "verification": a.verification,
                // REQ-020 stable identity + its honesty flags (FEAT-077/087):
                // a consumer may treat a missing key in a later build as
                // "site gone" ONLY when !id_build_local &&
                // ident_survives_own_edit; otherwise `uncertain` (REQ-021).
                "obligation_id": a.obligation_id,
                "site_key": a.site_key,
                "group_key": a.group_key,
                "id_build_local": a.id_build_local,
                "ident_survives_own_edit": a.ident_survives_own_edit
            })
        })
        .collect();
    let payload = json!({
        "total_matches": total,
        "truncated": total > shown.len(),
        "matches": shown
    });
    tool_result(id, &payload)
}

#[cfg(test)]
mod tests {
    use super::handle_line;
    use serde_json::{Value, json};
    use std::path::PathBuf;

    /// Fixture chosen so ALL the surfaces the tools summarize are non-empty:
    /// `$div_unknown` divides by an unknown param (PotentialTrap →
    /// UnprovenObligation `div-by-zero`), `$div_const` divides by 7
    /// (ProvenSafe → LeverageableFact `proven-safe`), `$branchy` has a
    /// `br_table` (UnmodeledBranch gap → PrecisionGap `unmodeled-branch`).
    const FIXTURE_WAT: &str = r#"
(module
  (func $div_unknown (export "div_unknown") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.div_u)
  (func $div_const (export "div_const") (param i32) (result i32)
    local.get 0
    i32.const 7
    i32.div_u)
  (func $branchy (export "branchy") (param i32) (result i32)
    (block
      (block
        local.get 0
        br_table 0 1 0))
    i32.const 2)
)
"#;

    /// Write the fixture to a temp `.wat` path the tools can be pointed at.
    fn fixture_path(tag: &str) -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "scry_mcp_fixture_{}_{}.wat",
            tag,
            std::process::id()
        ));
        std::fs::write(&p, FIXTURE_WAT).unwrap();
        p
    }

    /// The fixture's analysis, run DIRECTLY through the library — the ground
    /// truth the tool responses are compared against (non-vacuity: every count
    /// asserted on the tool output is first asserted non-trivial here).
    fn ground_truth() -> scry_analyze_core::AnalysisResult {
        let bytes = wat::parse_str(FIXTURE_WAT).unwrap();
        scry_analyze_core::analyze(bytes, scry_analyze_core::AnalysisConfig::default()).unwrap()
    }

    fn rpc(id: u64, method: &str, params: Value) -> String {
        json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}).to_string()
    }

    /// Send one request line, parse the one response line.
    fn roundtrip(line: &str) -> Value {
        let resp = handle_line(line).expect("request with an id must get a response");
        serde_json::from_str(&resp).expect("response must be valid JSON")
    }

    fn call_tool(name: &str, args: Value) -> Value {
        roundtrip(&rpc(
            7,
            "tools/call",
            json!({"name": name, "arguments": args}),
        ))
    }

    /// A tool result's structured payload: the JSON re-parsed from the text
    /// content block (agents read exactly this).
    fn tool_payload(resp: &Value) -> Value {
        let result = resp.get("result").unwrap_or_else(|| {
            panic!("expected a result, got: {resp}");
        });
        assert_ne!(
            result.get("isError").and_then(Value::as_bool),
            Some(true),
            "tool call unexpectedly errored: {result}"
        );
        let text = result["content"][0]["text"]
            .as_str()
            .expect("content[0].text must be a string");
        serde_json::from_str(text).expect("tool text content must itself be structured JSON")
    }

    // ── initialize ────────────────────────────────────────────────────────

    #[test]
    fn initialize_reports_server_info_and_tools_capability() {
        let resp = roundtrip(&rpc(
            1,
            "initialize",
            json!({"protocolVersion": "2025-06-18", "capabilities": {},
                   "clientInfo": {"name": "test", "version": "0"}}),
        ));
        let result = &resp["result"];
        assert!(
            result["protocolVersion"].is_string(),
            "initialize must report a protocolVersion, got: {resp}"
        );
        assert_eq!(result["serverInfo"]["name"], "scry-mcp");
        assert!(
            result["capabilities"]["tools"].is_object(),
            "server must declare the tools capability, got: {resp}"
        );
    }

    // ── tools/list (AC#2 lives here) ──────────────────────────────────────

    #[test]
    fn tools_list_is_analyze_and_query_and_verify_is_absent() {
        let resp = roundtrip(&rpc(2, "tools/list", json!({})));
        let tools = resp["result"]["tools"]
            .as_array()
            .unwrap_or_else(|| panic!("tools/list must return a tools array, got: {resp}"));
        let names: Vec<&str> = tools
            .iter()
            .map(|t| t["name"].as_str().expect("every tool has a name"))
            .collect();
        // Non-vacuity: the enumeration is non-empty (an empty list would make
        // the absence assert below pass while the server exposes nothing).
        assert!(!names.is_empty(), "tools/list returned no tools");
        // The v3.3.0 surface, exactly.
        assert_eq!(names, vec!["analyze", "query"]);
        // FEAT-066 AC#2, asserted in its own words: `verify` is ABSENT from
        // the actual tools/list payload — the deferral is enforced by the
        // tool list, not by documentation.
        assert!(
            !names.contains(&"verify"),
            "verify must be ABSENT from the v3.3.0 tool list (REQ-021)"
        );
        // Every listed tool is callable-by-schema: name + description +
        // an object inputSchema (what an MCP client renders to the model).
        for t in tools {
            assert!(t["description"].as_str().is_some_and(|d| !d.is_empty()));
            assert_eq!(t["inputSchema"]["type"], "object");
        }
    }

    #[test]
    fn calling_verify_is_rejected_as_unknown_tool() {
        let p = fixture_path("verify");
        let resp = call_tool("verify", json!({"module_path": p}));
        let err = resp
            .get("error")
            .unwrap_or_else(|| panic!("verify must be rejected, got: {resp}"));
        assert_eq!(err["code"], -32602);
        assert!(
            err["message"].as_str().unwrap().contains("verify"),
            "error should name the unknown tool, got: {err}"
        );
    }

    // ── analyze (AC#1) ────────────────────────────────────────────────────

    #[test]
    fn analyze_returns_structured_summary_matching_ground_truth() {
        let truth = ground_truth();
        // Non-vacuity: the fixture genuinely exercises every summarized
        // surface, so a summary of zeros CANNOT pass.
        use scry_analyze_core::{AdvisoryClass, TrapVerdict};
        let n_unproven = truth
            .advisories
            .iter()
            .filter(|a| a.class == AdvisoryClass::UnprovenObligation)
            .count();
        let n_fact = truth
            .advisories
            .iter()
            .filter(|a| a.class == AdvisoryClass::LeverageableFact)
            .count();
        let n_gap_class = truth
            .advisories
            .iter()
            .filter(|a| a.class == AdvisoryClass::PrecisionGap)
            .count();
        let n_potential = truth
            .trap_checks
            .iter()
            .filter(|t| t.verdict == TrapVerdict::PotentialTrap)
            .count();
        let n_safe = truth
            .trap_checks
            .iter()
            .filter(|t| t.verdict == TrapVerdict::ProvenSafe)
            .count();
        assert!(n_unproven > 0 && n_fact > 0 && n_gap_class > 0);
        assert!(n_potential > 0 && n_safe > 0);
        assert!(!truth.gaps.is_empty());

        let p = fixture_path("analyze");
        let resp = call_tool("analyze", json!({"module_path": p}));
        let s = tool_payload(&resp);

        assert_eq!(s["functions"], truth.function_summaries.len());
        assert_eq!(s["advisories"]["total"], truth.advisories.len());
        assert_eq!(
            s["advisories"]["by_class"]["unproven-obligation"],
            n_unproven
        );
        assert_eq!(s["advisories"]["by_class"]["leverageable-fact"], n_fact);
        assert_eq!(s["advisories"]["by_class"]["precision-gap"], n_gap_class);
        assert_eq!(s["advisories"]["by_class"]["definite-fault"], 0);
        assert_eq!(s["trap_checks"]["total"], truth.trap_checks.len());
        assert_eq!(s["trap_checks"]["potential-trap"], n_potential);
        assert_eq!(s["trap_checks"]["proven-safe"], n_safe);
        assert_eq!(s["gaps"]["total"], truth.gaps.len());
        assert_eq!(s["gaps"]["by_kind"]["unmodeled-branch"], truth.gaps.len());

        // AC#1 structural: a SUMMARY, not a dump and not HTML. The advisories
        // field is an object of counts (no per-site array), the serialized
        // text is small, and there is no markup.
        let text = resp["result"]["content"][0]["text"].as_str().unwrap();
        assert!(s["advisories"].is_object() && !s["advisories"].is_array());
        assert!(
            text.len() < 16 * 1024,
            "analyze summary must stay small, got {} bytes",
            text.len()
        );
        assert!(!text.contains("<html") && !text.contains("<!doctype") && !text.contains("<div"));
    }

    #[test]
    fn analyze_missing_file_is_a_tool_error_not_a_crash() {
        let resp = call_tool("analyze", json!({"module_path": "/nonexistent/xyz.wasm"}));
        let result = &resp["result"];
        assert_eq!(
            result["isError"], true,
            "a bad path must surface as an in-band tool error, got: {resp}"
        );
        assert!(result["content"][0]["text"].as_str().is_some());
    }

    #[test]
    fn analyze_without_module_path_is_invalid_params() {
        let resp = call_tool("analyze", json!({}));
        assert_eq!(resp["error"]["code"], -32602, "got: {resp}");
    }

    // ── query ─────────────────────────────────────────────────────────────

    #[test]
    fn query_filters_match_ground_truth_and_never_widen() {
        let truth = ground_truth();
        let n_all = truth.advisories.len();
        let n_div = truth
            .advisories
            .iter()
            .filter(|a| a.code == "div-by-zero")
            .count();
        // Non-vacuity: the code filter selects a PROPER non-empty subset, so
        // both "filter works" and "filter is not a no-op" are observable.
        assert!(n_div > 0, "fixture must produce a div-by-zero advisory");
        assert!(n_all > n_div, "fixture must also produce OTHER advisories");

        let p = fixture_path("query");
        let s = tool_payload(&call_tool(
            "query",
            json!({"module_path": p, "code": "div-by-zero"}),
        ));
        assert_eq!(s["total_matches"], n_div);
        let matches = s["matches"].as_array().unwrap();
        assert_eq!(matches.len(), n_div);
        for m in matches {
            assert_eq!(m["code"], "div-by-zero");
            assert_eq!(m["class"], "unproven-obligation");
            assert!(m["func_index"].is_u64() && m["pc"].is_u64());
            // REQ-020: each match carries its stable obligation identity.
            assert!(m["obligation_id"].as_str().is_some());
        }

        // Class filter, on a different class than the code filter above.
        let s = tool_payload(&call_tool(
            "query",
            json!({"module_path": p, "class": "leverageable-fact"}),
        ));
        let n_fact = truth
            .advisories
            .iter()
            .filter(|a| a.class == scry_analyze_core::AdvisoryClass::LeverageableFact)
            .count();
        assert!(n_fact > 0);
        assert_eq!(s["total_matches"], n_fact);

        // A code the fixture does NOT produce: zero matches, while the module
        // demonstrably has advisories (asserted above) — the filter filters.
        let s = tool_payload(&call_tool(
            "query",
            json!({"module_path": p, "code": "use-after-drop"}),
        ));
        assert_eq!(s["total_matches"], 0);
        assert_eq!(s["matches"].as_array().unwrap().len(), 0);

        // Unconstrained query selects everything (Query::default semantics).
        let s = tool_payload(&call_tool("query", json!({"module_path": p})));
        assert_eq!(s["total_matches"], n_all);
    }

    #[test]
    fn query_limit_caps_matches_but_reports_total() {
        let truth = ground_truth();
        let n_all = truth.advisories.len();
        assert!(
            n_all > 1,
            "fixture must have more advisories than the limit"
        );
        let p = fixture_path("limit");
        let s = tool_payload(&call_tool("query", json!({"module_path": p, "limit": 1})));
        assert_eq!(s["matches"].as_array().unwrap().len(), 1);
        assert_eq!(s["total_matches"], n_all);
        assert_eq!(s["truncated"], true);
    }

    #[test]
    fn query_rejects_an_unknown_class_value() {
        let p = fixture_path("badclass");
        let resp = call_tool("query", json!({"module_path": p, "class": "no-such-class"}));
        assert_eq!(resp["error"]["code"], -32602, "got: {resp}");
    }

    // ── protocol plumbing ─────────────────────────────────────────────────

    #[test]
    fn parse_error_unknown_method_and_notification() {
        // Malformed JSON → -32700 with a null id.
        let resp: Value = roundtrip("{not json");
        assert_eq!(resp["error"]["code"], -32700);
        assert!(resp["id"].is_null());

        // Unknown method with an id → -32601.
        let resp = roundtrip(&rpc(9, "no/such/method", json!({})));
        assert_eq!(resp["error"]["code"], -32601);
        assert_eq!(resp["id"], 9);

        // A notification (no id) gets NO response — MCP clients send
        // notifications/initialized and a reply would corrupt the stream.
        let note = json!({"jsonrpc": "2.0", "method": "notifications/initialized"}).to_string();
        assert_eq!(handle_line(&note), None);
    }
}
