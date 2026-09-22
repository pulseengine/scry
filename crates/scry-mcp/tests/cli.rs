//! PulseEngine CLI conventions 1 and 2, asserted against the real binary.
//!
//! Convention 1: `--version` and `-V` print `<binary-name> <semver>` and exit 0.
//!   "A tool that cannot state its own version cannot appear in evidence."
//! Convention 2: `--help` exits 0; an unknown flag exits 2 with usage on stderr.
//!
//! These run the BINARY, not a parse function, because the contract is about
//! the process: an agent runtime launching `scry-mcp --version` must get a
//! version and an exit, not a started stdio server.
use std::process::{Command, Stdio};

fn run(args: &[&str]) -> (i32, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_scry-mcp"))
        .args(args)
        .stdin(Stdio::null()) // never let it block on the protocol stream
        .output()
        .expect("spawn scry-mcp");
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
            format!("scry-mcp {}", env!("CARGO_PKG_VERSION")),
            "{flag} must print `<binary-name> <semver>`; got {line:?}"
        );
    }
}

#[test]
fn help_exits_zero_and_says_something() {
    let (code, stdout, stderr) = run(&["--help"]);
    assert_eq!(code, 0, "--help must exit 0 (convention 2)");
    assert!(
        stdout.contains("scry-mcp") || stderr.contains("scry-mcp"),
        "--help must print usage naming the binary"
    );
}

#[test]
fn unknown_flag_exits_two_with_usage_on_stderr() {
    let (code, _, stderr) = run(&["--definitely-not-a-flag"]);
    assert_eq!(code, 2, "an unknown flag must exit 2 (convention 2)");
    assert!(
        !stderr.trim().is_empty(),
        "an unknown flag must say something on stderr"
    );
}

/// The regression that motivates all of the above: before this, EVERY flag —
/// including `--version` — fell through to the stdio loop and started the
/// server. An agent probing the binary got a hung process, not a version.
#[test]
fn a_flag_does_not_silently_start_the_server() {
    let (code, stdout, _) = run(&["--version"]);
    assert_eq!(code, 0);
    assert!(
        !stdout.trim().is_empty(),
        "`--version` produced NO output — the argv path is being ignored again"
    );
}
