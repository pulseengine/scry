#!/usr/bin/env python3
"""Gate: a safety goal with no supporting evidence must be DECLARED undeveloped,
and that declaration must be justified.

WHY THIS EXISTS (J-004, scry safety case). `rivet coverage` reports
goal-has-support at 40% and cannot distinguish a goal deliberately marked
`undeveloped: true` — GSN's diamond — from one somebody simply forgot. Both
render identically. J-004 records that the 40% was investigated and is
intentional, but a justification is prose: the next unsupported goal added to
the repo would hide among the declared ones and read exactly the same.

So this checks two directions, not one:

  (1) a goal with NO supporting safety-solution MUST carry `undeveloped: true`
      -- catches a goal someone forgot to develop or to declare;
  (2) a goal carrying `undeveloped: true` MUST be named by a safety-justification
      -- catches the flag being added to quiet the report, which is the shape a
      forgotten goal takes once someone notices the number.

(2) is the one that matters. (1) alone is satisfiable by typing the flag.

NOT WHAT THIS DOES: it does not make `rivet coverage`'s 40% meaningful. That
figure still counts declared-undeveloped goals as uncovered and still prints
40%. This gate closes one direction only -- forgotten hiding among declared.
"""
import sys, json, glob, subprocess, tempfile, os

try:
    import yaml
except ImportError:
    # FAIL CLOSED. A gate that silently skips when a dependency is missing
    # reports green while checking nothing -- the scry#141 failure mode. CI
    # installs PyYAML explicitly; if it is absent, that is a broken gate, not
    # a passing build.
    print("FAIL: PyYAML not available -- this gate cannot run", file=sys.stderr)
    sys.exit(1)


def load_docs(paths):
    arts = []
    for p in paths:
        try:
            d = yaml.safe_load(open(p, encoding="utf-8"))
        except Exception as e:
            print(f"  WARN: unparseable {p}: {e}", file=sys.stderr)
            continue
        if isinstance(d, dict):
            arts.extend(d.get("artifacts") or [])
    return [a for a in arts if isinstance(a, dict) and a.get("id")]


def links_of(a):
    return [l for l in (a.get("links") or []) if isinstance(l, dict)]


def check(arts):
    """Return a list of violation strings. Pure: the self-test drives this too."""
    goals = [a for a in arts if a.get("type") == "safety-goal"]
    supported = set()
    for a in arts:
        if a.get("type") == "safety-solution":
            for l in links_of(a):
                if l.get("type") == "supports":
                    supported.add(l.get("target"))
    justified = set()
    for a in arts:
        if a.get("type") != "safety-justification":
            continue
        for l in links_of(a):
            if l.get("type") == "justifies":
                justified.add(l.get("target"))
        blob = json.dumps(a)  # rationale/description text may name the goal
        for g in goals:
            if g["id"] in blob:
                justified.add(g["id"])

    bad = []
    for g in sorted(goals, key=lambda x: x["id"]):
        gid = g["id"]
        undev = bool((g.get("fields") or {}).get("undeveloped"))
        if gid not in supported and not undev:
            bad.append(
                f"{gid}: no safety-solution supports it and it is NOT declared "
                f"`undeveloped: true` -- develop it, or declare it deliberately"
            )
        if undev and gid not in justified:
            bad.append(
                f"{gid}: declared `undeveloped: true` but NO safety-justification "
                f"names it -- an undeclared gap is hiding behind the flag"
            )
    return bad, goals


def self_test():
    """Feed the checker inputs it MUST reject, and one it must accept."""
    ok = lambda a: check(a)[0]
    sol = lambda t: {"id": "Sn-x", "type": "safety-solution",
                     "links": [{"type": "supports", "target": t}]}
    jus = lambda t: {"id": "J-x", "type": "safety-justification",
                     "links": [{"type": "justifies", "target": t}]}
    goal = lambda i, u=None: {"id": i, "type": "safety-goal",
                              "fields": ({"undeveloped": u} if u is not None else {})}
    cases = [
        ("healthy: supported goal", [goal("G-1"), sol("G-1")], 0),
        ("healthy: undeveloped AND justified", [goal("G-2", True), jus("G-2")], 0),
        ("REJECT: unsupported, not declared", [goal("G-3")], 1),
        # The case J-004 actually warns about: the flag added to quiet the
        # report, with nothing explaining it. A checker that misses this only
        # catches the mistake nobody was going to make.
        ("REJECT: undeveloped but unjustified", [goal("G-4", True)], 1),
        ("REJECT: both faults on one goal is still caught",
         [goal("G-5"), goal("G-6", True)], 2),
    ]
    failed = 0
    for name, arts, want in cases:
        got = len(ok(arts))
        status = "ok" if got == want else "SELF-TEST FAILED"
        if got != want:
            failed += 1
        print(f"  [{status}] {name}: {got} violation(s), expected {want}")
    # A justification that names the goal only in prose must also count.
    prose = [goal("G-7", True),
             {"id": "J-y", "type": "safety-justification",
              "fields": {"rationale": "G-7 is deliberately undeveloped because ..."}}]
    got = len(ok(prose))
    print(f"  [{'ok' if got==0 else 'SELF-TEST FAILED'}] prose-only justification counts: {got} violation(s), expected 0")
    failed += got != 0
    return failed


def main():
    if "--self-test" in sys.argv:
        f = self_test()
        print("SELF-TEST PASS" if not f else f"SELF-TEST FAIL ({f})")
        return 1 if f else 0

    paths = sorted(glob.glob("artifacts/**/*.yaml", recursive=True))
    arts = load_docs(paths)
    bad, goals = check(arts)
    print(f"  scanned {len(paths)} artifact file(s); found {len(goals)} safety-goal(s)")

    # A checker that reads one file would silently omit G-005 (it lives in
    # roadmap-2.0.yaml, not safety-case.yaml). Cross-check the population
    # against rivet so this checker cannot have the bug it exists to prevent.
    try:
        out = subprocess.run(["rivet", "list", "--format", "json"],
                             capture_output=True, text=True, timeout=120)
        if out.returncode == 0:
            d = json.loads(out.stdout)
            items = d if isinstance(d, list) else d.get("artifacts", d.get("items", []))
            n = sum(1 for a in items if a.get("type") == "safety-goal")
            if n != len(goals):
                print(f"  FAIL: rivet sees {n} safety-goals, this checker sees "
                      f"{len(goals)} -- the scan is missing a file")
                return 1
            print(f"  cross-check: rivet agrees ({n} safety-goals)")
    except Exception as e:
        print(f"  WARN: rivet cross-check skipped ({e})", file=sys.stderr)

    for b in bad:
        print(f"  FAIL: {b}")
    print("PASS" if not bad else f"FAIL ({len(bad)} violation(s))")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
