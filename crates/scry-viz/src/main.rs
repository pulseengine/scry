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
