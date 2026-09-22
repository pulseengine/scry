//! `scry-mcp` binary — MCP server over stdio (FEAT-066).
//!
//! Reads newline-delimited JSON-RPC 2.0 messages from stdin, writes one
//! response line per request to stdout (notifications get no response).
//! All logging goes to stderr: stdout is the protocol stream and a stray
//! line there corrupts it.
//!
//! Wire up in an MCP client config as a stdio server, e.g.:
//! `{ "command": "scry-mcp" }` — then call the `analyze` / `query` tools.

use std::io::{BufRead, Write};

const USAGE: &str = "\
usage: scry-mcp

An MCP (Model Context Protocol) server for the scry sound abstract
interpreter. Speaks JSON-RPC 2.0 over stdio; takes no arguments. Wire it
into an MCP client config as a stdio server, e.g. { \"command\": \"scry-mcp\" },
then call the `analyze` and `query` tools.

  -V, --version   print version and exit
  -h, --help      print this help and exit";

/// PulseEngine CLI conventions 1 and 2. Before this existed, EVERY argument —
/// `--version` included — fell through to the stdio loop below and started the
/// server, so an agent runtime probing the binary got a hung process instead of
/// a version string. A tool that cannot state its own version cannot appear in
/// evidence, and scry#DD-023 makes this binary a shipped artifact.
fn handle_args() -> Option<i32> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        return None; // no arguments: run the server (the normal path)
    }
    match args[0].as_str() {
        "-V" | "--version" => {
            println!("scry-mcp {}", env!("CARGO_PKG_VERSION"));
            Some(0)
        }
        "-h" | "--help" => {
            println!("{USAGE}");
            Some(0)
        }
        other => {
            eprintln!("scry-mcp: unknown argument: {other}");
            eprintln!("{USAGE}");
            Some(2)
        }
    }
}

fn main() {
    if let Some(code) = handle_args() {
        std::process::exit(code);
    }
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();
    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(e) => {
                eprintln!("scry-mcp: stdin read error: {e}");
                break;
            }
        };
        if line.trim().is_empty() {
            continue;
        }
        if let Some(resp) = scry_mcp::handle_line(&line) {
            // A write/flush failure means the client hung up; exit quietly.
            if writeln!(stdout, "{resp}")
                .and_then(|()| stdout.flush())
                .is_err()
            {
                break;
            }
        }
    }
}
