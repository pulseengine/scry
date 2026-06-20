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
    match run(&args) {
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
