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

fn main() {
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
