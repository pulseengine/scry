//! PulseEngine CLI conventions 1 and 2, asserted against the real binary.
//! See crates/scry-mcp/tests/cli.rs for the same contract on the MCP server.
use std::process::{Command, Stdio};

fn run(args: &[&str]) -> (i32, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_scry-viz"))
        .args(args)
        .stdin(Stdio::null())
        .output()
        .expect("spawn scry-viz");
    (
        out.status.code().expect("exit code"),
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn version_flags_print_name_and_semver_and_exit_zero() {
    for flag in ["--version", "-V"] {
        let (code, stdout, _) = run(&[flag]);
        assert_eq!(code, 0, "{flag} must exit 0");
        let line = stdout.lines().next().unwrap_or_default().trim().to_string();
        assert_eq!(
            line,
            format!("scry-viz {}", env!("CARGO_PKG_VERSION")),
            "{flag} must print `<binary-name> <semver>`; got {line:?}"
        );
    }
}

/// The regression: `--help` returned `err(2, usage)`, i.e. it exited 2 and
/// printed to stderr — help treated as a usage ERROR. Convention 2 says help
/// is a successful request for help.
#[test]
fn help_exits_zero() {
    for flag in ["-h", "--help"] {
        let (code, stdout, _) = run(&[flag]);
        assert_eq!(code, 0, "{flag} must exit 0, not 2");
        assert!(
            stdout.contains("usage"),
            "{flag} must print usage on STDOUT; got {stdout:?}"
        );
    }
}

#[test]
fn unknown_flag_still_exits_two_with_stderr() {
    let (code, _, stderr) = run(&["--definitely-not-a-flag"]);
    assert_eq!(code, 2, "an unknown flag must exit 2");
    assert!(stderr.contains("unknown flag"), "must name the bad flag");
}

/// Control: the fix must not turn every exit into 0. A real usage error — no
/// input module — must still be 2.
#[test]
fn a_genuine_usage_error_still_exits_two() {
    let (code, _, stderr) = run(&[]);
    assert_eq!(code, 2, "no input must still be a usage error");
    assert!(!stderr.trim().is_empty());
}
