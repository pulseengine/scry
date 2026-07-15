//! `scry-viz` CLI — analyze a Core Wasm module and write a static HTML page.
//!
//! ```text
//! scry-viz <input.wasm|input.wat> [-o output.html] [--title NAME]
//! ```
//!
//! Accepts either a binary `.wasm` module or a `.wat` text module (assembled
//! in-process). With no `-o`, writes `<input-stem>.html` next to the input.
//! Exit codes: 0 ok, 2 usage error, 3 analysis error, 4 I/O error.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use scry_analyze_core::{AnalysisConfig, analyze};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    // `scry-viz check <module>` is a well-formedness gate (its own exit code,
    // no file output), so it's dispatched before the file-writing forms.
    if args.first().map(String::as_str) == Some("check") {
        return run_check(&args[1..]);
    }
    // Subcommand dispatch: `scry-viz index ...` builds a landing page; the
    // bare form `scry-viz <input> ...` renders one analysis.
    let result = match args.first().map(String::as_str) {
        Some("index") => run_index(&args[1..]),
        _ => run(&args),
    };
    match result {
        Ok(out) => {
            eprintln!("scry-viz: wrote {}", out.display());
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("scry-viz: {}", e.msg);
            ExitCode::from(e.code)
        }
    }
}

/// `scry-viz check <input.wasm|input.wat>` — FEAT-031 well-formedness gate.
/// Analyzes the module and runs `scry_viz::check_wellformed`; prints the
/// violations and exits non-zero (5) if any, else prints an OK line and exits
/// 0. Used in CI as a robustness gate on scry's own compiled module.
fn run_check(args: &[String]) -> ExitCode {
    let path = match args.iter().find(|a| !a.starts_with('-')) {
        Some(p) => PathBuf::from(p),
        None => {
            eprintln!("scry-viz: usage: scry-viz check <input.wasm|input.wat>");
            return ExitCode::from(2);
        }
    };
    let bytes = match read_module(&path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("scry-viz: {}", e.msg);
            return ExitCode::from(e.code);
        }
    };
    let result = match analyze(
        bytes,
        AnalysisConfig {
            emit_diagnostics: true,
            ..Default::default()
        },
    ) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("scry-viz check: analysis failed: {e:?}");
            return ExitCode::from(3);
        }
    };
    let violations = scry_viz::check_wellformed(&result);
    if violations.is_empty() {
        eprintln!(
            "scry-viz check: OK — {} functions, {} program points, {} call edges well-formed",
            result.function_meta.len(),
            result.invariants.points.len(),
            result.call_graph.len(),
        );
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "scry-viz check: {} well-formedness violation(s):",
            violations.len()
        );
        for v in &violations {
            eprintln!("  - {v}");
        }
        ExitCode::from(5)
    }
}

struct CliError {
    msg: String,
    code: u8,
}

fn err(code: u8, msg: impl Into<String>) -> CliError {
    CliError {
        msg: msg.into(),
        code,
    }
}

fn run(args: &[String]) -> Result<PathBuf, CliError> {
    let mut input: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut title: Option<String> = None;

    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "-h" | "--help" => {
                return Err(err(
                    2,
                    "usage: scry-viz <input.wasm|input.wat> [-o output.html] [--title NAME]",
                ));
            }
            "-o" | "--output" => {
                output = Some(PathBuf::from(
                    it.next().ok_or_else(|| err(2, "-o needs a path"))?,
                ));
            }
            "--title" => {
                title = Some(
                    it.next()
                        .ok_or_else(|| err(2, "--title needs a value"))?
                        .clone(),
                );
            }
            other if other.starts_with('-') => {
                return Err(err(2, format!("unknown flag: {other}")));
            }
            other => {
                if input.is_some() {
                    return Err(err(2, "more than one input given"));
                }
                input = Some(PathBuf::from(other));
            }
        }
    }

    let input = input.ok_or_else(|| err(2, "no input module given (see --help)"))?;
    let bytes = read_module(&input)?;
    let title = title.unwrap_or_else(|| {
        input
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "module".to_string())
    });

    let result = analyze(
        bytes,
        AnalysisConfig {
            emit_diagnostics: true,
            ..Default::default()
        },
    )
    .map_err(|e| err(3, format!("analysis failed: {e:?}")))?;

    let html = scry_viz::render_html(&result, &title);
    let out = output.unwrap_or_else(|| input.with_extension("html"));
    std::fs::write(&out, html).map_err(|e| err(4, format!("writing {}: {e}", out.display())))?;

    // Structured, machine-consumable feed alongside the HTML: `<stem>.guidance.json`
    // (the full, un-capped advisories + trap verdicts an AI-agent consumer reads).
    let json = scry_viz::render_guidance_json(&result);
    let json_out = out.with_extension("guidance.json");
    std::fs::write(&json_out, json)
        .map_err(|e| err(4, format!("writing {}: {e}", json_out.display())))?;
    eprintln!("scry-viz: wrote {}", json_out.display());
    Ok(out)
}

/// `scry-viz index --site-dir DIR [--title NAME]` — write a landing
/// `index.html` into DIR linking the known dashboard views that exist there
/// (the scry-viz self-analysis and the MC/DC dashboard). Only views actually
/// present on disk are linked, so a partial build still yields a valid page.
fn run_index(args: &[String]) -> Result<PathBuf, CliError> {
    let mut site_dir: Option<PathBuf> = None;
    let mut title: Option<String> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "-h" | "--help" => {
                return Err(err(
                    2,
                    "usage: scry-viz index --site-dir DIR [--title NAME]",
                ));
            }
            "--site-dir" => {
                site_dir = Some(PathBuf::from(
                    it.next().ok_or_else(|| err(2, "--site-dir needs a path"))?,
                ));
            }
            "--title" => {
                title = Some(
                    it.next()
                        .ok_or_else(|| err(2, "--title needs a value"))?
                        .clone(),
                );
            }
            other => return Err(err(2, format!("unknown index arg: {other}"))),
        }
    }
    let site_dir = site_dir.ok_or_else(|| err(2, "index needs --site-dir DIR"))?;
    let title = title.unwrap_or_else(|| "scry verification dashboard".to_string());

    // Known views, in display order. (relative href, on-disk probe, title, description)
    let known: &[(&str, &str, &str, &str)] = &[
        (
            "self-analysis.html",
            "self-analysis.html",
            "Self-analysis (scry on scry)",
            "scry analyzing its own compiled module — functions, call graph, \
             diagnostics, and per-program-point invariants (locals + operand stack).",
        ),
        (
            "mcdc/index.html",
            "mcdc/index.html",
            "MC/DC truth-table dashboard",
            "witness-viz coverage of scry's real analyzer decision corpus.",
        ),
    ];
    let entries: Vec<scry_viz::IndexEntry> = known
        .iter()
        .filter(|(_, probe, _, _)| site_dir.join(probe).exists())
        .map(|(href, _, t, d)| scry_viz::IndexEntry {
            href: (*href).to_string(),
            title: (*t).to_string(),
            description: (*d).to_string(),
        })
        .collect();

    let html = scry_viz::render_index(&title, &entries);
    let out = site_dir.join("index.html");
    std::fs::write(&out, html).map_err(|e| err(4, format!("writing {}: {e}", out.display())))?;
    Ok(out)
}

/// Read a module, assembling `.wat`/`.wast` text to bytes; otherwise treat the
/// file as raw `.wasm`.
fn read_module(path: &Path) -> Result<Vec<u8>, CliError> {
    let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    if ext == "wat" || ext == "wast" {
        wat::parse_file(path).map_err(|e| err(4, format!("assembling {}: {e}", path.display())))
    } else {
        std::fs::read(path).map_err(|e| err(4, format!("reading {}: {e}", path.display())))
    }
}
