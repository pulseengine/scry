#!/usr/bin/env python3
"""Gate: commits touching traced paths must link an artifact that RESOLVES.

WHY (scry#161). rivet ships commit-to-artifact traceability and it was never
configured, so the V-model's artifact side and the code side were not connected
at all. The counter that earns its keep is `broken_refs` -- a commit naming an
artifact id that does not exist. That is precisely how PR #159 merged
referencing FEAT-086 before the artifact existed (#160): found by grepping,
not by a gate.

WHY NOT `rivet commits --strict`. Measured: --strict also promotes the
repo-wide "unimplemented artifacts" warning, which reports
`Artifact coverage: 1/257` and CANNOT be satisfied by any pull request. A gate
no PR can pass gets switched off. This checks only the counters a PR is
responsible for -- its own commits -- and deliberately ignores `unimplemented`
and `artifact_coverage`.

FORWARD-ONLY by construction: scoped to a commit RANGE, so the 85 pre-existing
orphans never enter the gate.
"""
import sys, json, subprocess

FATAL = ("orphans", "broken_refs", "malformed_refs")

WHY = {
    "orphans": "commit touches a traced path but links no artifact "
               "(add e.g. `Refs: FEAT-091`, or `Trace: skip`)",
    "broken_refs": "commit names an artifact id that does NOT resolve "
                   "(the scry#160 defect: referencing an artifact before it exists)",
    "malformed_refs": "trailer key not recognised -- note rivet's matcher is FUZZY "
                      "and will read a prose line like 'Verified: ...' as one",
}


def verdict(summary):
    """Pure: summary dict -> list of (counter, count, why). Drives --self-test."""
    return [(k, summary.get(k, 0), WHY[k]) for k in FATAL if summary.get(k, 0)]


def self_test():
    cases = [
        ("clean", {"orphans": 0, "broken_refs": 0, "malformed_refs": 0, "linked": 3}, 0),
        ("an orphan commit", {"orphans": 1, "broken_refs": 0, "malformed_refs": 0}, 1),
        ("a ref to a nonexistent artifact", {"orphans": 0, "broken_refs": 2, "malformed_refs": 0}, 1),
        ("a malformed trailer key", {"orphans": 0, "broken_refs": 0, "malformed_refs": 1}, 1),
        ("several at once are all reported", {"orphans": 1, "broken_refs": 1, "malformed_refs": 1}, 3),
        ("all-exempt range is clean", {"exempt": 9}, 0),
    ]
    bad = 0
    for name, s, want in cases:
        got = len(verdict(s))
        ok = got == want
        bad += not ok
        print(f"  [{'ok' if ok else 'SELF-TEST FAILED'}] {name}: {got} fatal, expected {want}")
    return bad


def main():
    if "--self-test" in sys.argv:
        f = self_test()
        print("SELF-TEST PASS" if not f else f"SELF-TEST FAIL ({f})")
        return 1 if f else 0

    rng = "origin/main..HEAD"
    if "--range" in sys.argv:
        rng = sys.argv[sys.argv.index("--range") + 1]

    try:
        out = subprocess.run(["rivet", "commits", "--range", rng, "--format", "json"],
                             capture_output=True, text=True, timeout=300)
    except Exception as e:
        # FAIL CLOSED: a gate that skips when its tool is missing reports green
        # while checking nothing (the scry#141 failure mode).
        print(f"FAIL: could not run rivet ({e})")
        return 1

    # Parse stdout REGARDLESS of exit code: rivet exits non-zero when a
    # reference is broken, and its JSON still carries the counters. Bailing on
    # returncode alone throws away the diagnostic naming WHICH counter failed.
    summary = None
    try:
        summary = json.loads(out.stdout)["summary"]
    except Exception:
        pass
    if summary is None:
        print(f"FAIL: rivet commits exited {out.returncode} with no parseable "
              f"summary\n{(out.stderr or out.stdout)[:500]}")
        return 1

    print(f"  range {rng}: {summary}")
    bad = verdict(summary)
    for k, n, why in bad:
        print(f"  FAIL: {k}={n} — {why}")
    print("PASS" if not bad else f"FAIL ({len(bad)} counter(s))")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
