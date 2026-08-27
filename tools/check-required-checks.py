#!/usr/bin/env python3
"""Gate: the ruleset's required checks must track the CI jobs that exist.

WHY (scry#130). `main` required NOTHING for months while `ci.yml` carried a
comment claiming three checks were required. The setting was fixed on
2026-08-27; this exists so it cannot silently rot again. Three ways it rots:

  1. A JOB IS ADDED and never required -> back to scry#130, one job at a time,
     with nobody noticing because the PR still goes green.
  2. A JOB IS RENAMED -> the old context is required forever, never reports,
     and every PR deadlocks.
  3. THE RULESET IS RESET -> it is named `temper-default-branch-protection`,
     i.e. something else may regenerate it. If required_status_checks vanishes,
     this fails loudly instead of quietly returning to advisory CI.

THE DEADLOCK RULE, which is why this is not just a set-equality check: a check
may be required only if it reports on EVERY pull request. A PATH-FILTERED
workflow (rivet-delta.yml: artifacts/**, rivet.yaml, ...) does not run on a
code-only PR, and a required check that never reports blocks that PR forever.
So path-filtered and `if:`-conditional jobs must NOT be required, and this
gate fails if one ever is.

NEW JOBS ARE NOT A FAILURE. A job added in the current PR does not yet exist on
main, so it cannot be required yet -- requiring it would deadlock every other
open PR. Those are reported as PENDING: add them to the ruleset after merge.
"""
import sys, json, subprocess

try:
    import yaml
except ImportError:
    print("FAIL: PyYAML not available -- this gate cannot run", file=sys.stderr)
    sys.exit(1)

# Deliberately excluded, with the reason, so the exclusion is auditable rather
# than folklore. Anything here MUST be path-filtered or conditional.
EXPECTED_EXCLUSIONS = {
    "Rivet artifact delta": "rivet-delta.yml is path-filtered; never reports on a code-only PR",
}


def workflow_jobs(text):
    """-> {job name: {'requirable': bool, 'why': str}} for one workflow file."""
    d = yaml.safe_load(text) or {}
    on = d.get("on", d.get(True)) or {}
    pr = on.get("pull_request") if isinstance(on, dict) else None
    path_filtered = bool(isinstance(pr, dict) and (pr.get("paths") or pr.get("paths-ignore")))
    runs_on_pr = pr is not None
    out = {}
    for jid, j in (d.get("jobs") or {}).items():
        if not isinstance(j, dict):
            continue
        name = j.get("name") or jid
        if not runs_on_pr:
            out[name] = (False, "does not run on pull_request")
        elif path_filtered:
            out[name] = (False, "workflow is path-filtered")
        elif j.get("if"):
            out[name] = (False, "job is `if:`-conditional")
        else:
            out[name] = (True, "")
    return out


def verdict(main_jobs, pr_jobs, required):
    """Pure -> (failures, pending). Drives --self-test."""
    fails, pending = [], []
    for name, (requirable, why) in main_jobs.items():
        if requirable and name not in required:
            fails.append(f"job {name!r} exists on main and runs on every PR, but is NOT required "
                         f"-- this is scry#130 returning one job at a time")
        if not requirable and name in required:
            fails.append(f"job {name!r} is required but {why} -- a check that does not report "
                         f"on every PR DEADLOCKS those PRs")
    all_names = set(main_jobs) | set(pr_jobs)
    for ctx in sorted(required):
        if ctx not in all_names:
            fails.append(f"required context {ctx!r} matches no job -- renamed or deleted; "
                         f"it can never report, so every PR deadlocks")
    for name, (requirable, _) in pr_jobs.items():
        if requirable and name not in main_jobs and name not in required:
            pending.append(name)
    for name, why in EXPECTED_EXCLUSIONS.items():
        if name in pr_jobs and pr_jobs[name][0]:
            fails.append(f"{name!r} is listed as a deliberate exclusion ({why}) but is now "
                         f"requirable -- the exclusion is stale, re-decide it")
    return fails, pending


def self_test():
    R = lambda: (True, "")
    N = lambda w: (False, w)
    cases = [
        ("clean: every main job required", {"A": R()}, {"A": R()}, {"A"}, 0, 0),
        ("a main job is NOT required (scry#130 returning)", {"A": R(), "B": R()}, {"A": R(), "B": R()}, {"A"}, 1, 0),
        ("a path-filtered job IS required (deadlock)", {"A": R(), "D": N("workflow is path-filtered")},
         {"A": R(), "D": N("x")}, {"A", "D"}, 1, 0),
        ("a required context matches no job (renamed)", {"A": R()}, {"A": R()}, {"A", "Gone"}, 1, 0),
        ("a NEW job in this PR is pending, not a failure", {"A": R()}, {"A": R(), "New": R()}, {"A"}, 0, 1),
        ("ruleset reset: nothing required at all", {"A": R(), "B": R()}, {"A": R(), "B": R()}, set(), 2, 0),
    ]
    bad = 0
    for name, mj, pj, req, wf, wp in cases:
        f, p = verdict(mj, pj, req)
        ok = len(f) == wf and len(p) == wp
        bad += not ok
        print(f"  [{'ok' if ok else 'SELF-TEST FAILED'}] {name}: {len(f)} fail / {len(p)} pending, "
              f"expected {wf}/{wp}")
    return bad


WORKFLOWS = [".github/workflows/ci.yml", ".github/workflows/rivet-delta.yml"]


def read(path, ref=None):
    if ref is None:
        return open(path, encoding="utf-8").read()
    r = subprocess.run(["git", "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def main():
    if "--self-test" in sys.argv:
        f = self_test()
        print("SELF-TEST PASS" if not f else f"SELF-TEST FAIL ({f})")
        return 1 if f else 0

    try:
        out = subprocess.run(
            ["gh", "api", "repos/pulseengine/scry/rulesets/16891064"],
            capture_output=True, text=True, timeout=120)
        rs = json.loads(out.stdout)
        rule = next((r for r in rs["rules"] if r["type"] == "required_status_checks"), None)
    except Exception as e:
        # FAIL CLOSED: unable to read the ruleset is not evidence it is correct.
        print(f"FAIL: could not read the ruleset ({e}). CI needs `permissions: "
              f"administration: read`.")
        return 1
    if rule is None:
        print("FAIL: the ruleset has NO required_status_checks rule -- this is exactly "
              "scry#130, and it was fixed on 2026-08-27. Something reset it.")
        return 1
    required = {c["context"] for c in rule["parameters"]["required_status_checks"]}

    main_jobs, pr_jobs = {}, {}
    for wf in WORKFLOWS:
        main_jobs.update(workflow_jobs(read(wf, "origin/main")))
        pr_jobs.update(workflow_jobs(read(wf)))
    if not main_jobs:
        print("FAIL: could not read any workflow from origin/main (shallow clone? "
              "needs fetch-depth: 0)")
        return 1

    print(f"  required contexts: {len(required)}; jobs on main: {len(main_jobs)}; "
          f"jobs in this PR: {len(pr_jobs)}")
    fails, pending = verdict(main_jobs, pr_jobs, required)
    for p in pending:
        print(f"  PENDING (not a failure): job {p!r} is new in this PR. Add it to the "
              f"ruleset AFTER merge -- requiring it now deadlocks every other open PR.")
    for f in fails:
        print(f"  FAIL: {f}")
    print("PASS" if not fails else f"FAIL ({len(fails)})")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
