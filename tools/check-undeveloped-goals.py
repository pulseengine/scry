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

SECOND POPULATION, SAME RULE (2026-08-28). The rule above generalises: AN
ABSENT THING MUST BE DECLARED AND JUSTIFIED. Safety goals are one population;
EMPTY COVERAGE RULES are another, and they fail in the more dangerous
direction because rivet renders an empty population as SUCCESS.

MEASURED: four of seventeen rules report 100.0% over 0/0 --
swe2-allocated-from-swe1, swe3-refines-swe2, swe4-verifies-swe3 and
swe3-has-verification -- plus the summary line
`V-closure: sw-detail-design (all 2 rules) 100.0% [0/0]`. Read row by row,
four rules announce success for work that was never done. scry cannot opt out:
the `aspice` preset is EMBEDDED and a project cannot subset its rule set.

The weighted overall does NOT inherit it (119/135 = 88.1%; an empty rule adds
0 to both sides), verified by `--fail-under 88.2` exiting 1 and `88.0` exiting
0. So the aggregate is safe to gate on and the per-row display is not.

Checked in BOTH directions against `.github/aspice-unmodelled-levels.txt`:
an empty population not listed there is an undeclared gap; a listed type whose
population is NOT empty is a stale entry and also fails. The second direction
is what stops the file becoming append-only, and it is what would catch a
rivet upgrade introducing a level we never populate -- which is the real
future event here, since the schema is pinned at aspice@0.2.0.
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


DECL_PATH = ".github/aspice-unmodelled-levels.txt"


def load_declared(text):
    """-> {source_type: reason}. Pure. A reason is REQUIRED (FEAT-088 rule 2)."""
    out, bad = {}, []
    for i, line in enumerate(text.split("\n"), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if ":" not in line:
            bad.append(f"{DECL_PATH}:{i}: no `<type>: <reason>` separator")
            continue
        k, v = line.split(":", 1)
        if not v.strip():
            bad.append(f"{DECL_PATH}:{i}: `{k.strip()}` declared with NO reason -- "
                       f"an unjustified declaration is what a forgotten gap looks like")
            continue
        out[k.strip()] = v.strip()
    return out, bad


def check_coverage(rules, declared):
    """-> list of violations. Pure: the self-test drives this too.

    BOTH directions. An empty population that is not declared is an undeclared
    gap wearing a 100%. A declared type whose population is NOT empty is a
    stale entry -- that direction is what keeps the file from becoming an
    append-only suppression list, and is the one that fires on a rivet upgrade.
    """
    empty, nonempty = set(), set()
    for r in rules:
        st = r.get("source_type")
        if st is None:
            continue
        (empty if r.get("total") == 0 else nonempty).add(st)
    # A type is only genuinely empty if NO rule over it has rows.
    empty -= nonempty

    bad = []
    for st in sorted(empty - set(declared)):
        names = sorted(r.get("name") for r in rules
                       if r.get("source_type") == st and r.get("total") == 0)
        bad.append(f"coverage population `{st}` is EMPTY, so rivet reports "
                   f"{', '.join(names)} at 100% over 0/0 -- populate it, or declare "
                   f"it in {DECL_PATH} with a reason")
    for st in sorted(set(declared) - empty):
        bad.append(f"`{st}` is declared unmodelled in {DECL_PATH} but its population "
                   f"is NOT empty -- remove the entry; a stale declaration makes the "
                   f"file a suppression list instead of a claim")
    return bad


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

    # ---- second population: empty coverage rules ----
    R = lambda n, st, tot: {"name": n, "source_type": st, "total": tot}
    cov_cases = [
        ("healthy: every rule has rows",
         [R("a", "x", 5), R("b", "y", 3)], {}, 0),
        ("REJECT: an empty population that is NOT declared",
         [R("a", "x", 5), R("b", "y", 0)], {}, 1),
        ("healthy: the same empty population, DECLARED",
         [R("a", "x", 5), R("b", "y", 0)], {"y": "reason"}, 0),
        # The direction that keeps the file from becoming append-only, and the
        # one that fires when a rivet upgrade populates a level we declared.
        ("REJECT: a STALE declaration whose population is not empty",
         [R("a", "x", 5)], {"x": "reason"}, 1),
        ("REJECT: declared type that appears in NO rule at all is still stale",
         [R("a", "x", 5)], {"zzz": "reason"}, 1),
        # A type with one empty rule and one populated rule is NOT empty; the
        # naive `any total==0` reading would wrongly demand a declaration.
        ("a type with one empty and one populated rule is not empty",
         [R("a", "x", 0), R("b", "x", 4)], {}, 0),
        ("two undeclared empty populations are both reported",
         [R("a", "x", 0), R("b", "y", 0)], {}, 2),
    ]
    for name, rules, decl, want in cov_cases:
        got = len(check_coverage(rules, decl))
        st = "ok" if got == want else "SELF-TEST FAILED"
        failed += got != want
        print(f"  [{st}] {name}: {got} violation(s), expected {want}")

    # ---- the declaration file parser ----
    decl_cases = [
        ("a reason is required", "a: because\nb:\n", 1),
        ("comments and blanks are skipped", "# note\n\na: because\n", 0),
        ("a line with no separator is rejected", "just-a-type\n", 1),
        ("a reason containing a colon survives", "a: see rivet: upstream\n", 0),
    ]
    for name, text, want in decl_cases:
        _, bad = load_declared(text)
        got = len(bad)
        st = "ok" if got == want else "SELF-TEST FAILED"
        failed += got != want
        print(f"  [{st}] decl-file: {name}: {got} problem(s), expected {want}")
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

    # ---- second population: coverage rules whose population is EMPTY ----
    # FAIL CLOSED throughout: this check exists because an empty rule renders
    # as 100%, so a checker that skips on an error would itself report green
    # while checking nothing (scry#141).
    try:
        text = open(DECL_PATH, encoding="utf-8").read()
    except OSError as e:
        print(f"  FAIL: cannot read {DECL_PATH} ({e}) -- the declaration file is "
              f"the whole basis of this check")
        return 1
    declared, decl_bad = load_declared(text)
    try:
        out = subprocess.run(["rivet", "coverage", "--format", "json"],
                             capture_output=True, text=True, timeout=180)
        if out.returncode != 0:
            print(f"  FAIL: `rivet coverage` exited {out.returncode}")
            return 1
        rules = json.loads(out.stdout).get("rules") or []
    except Exception as e:
        print(f"  FAIL: cannot read coverage rules ({e})")
        return 1
    if not rules:
        print("  FAIL: `rivet coverage` returned no rules -- nothing to check, "
              "which is not the same as nothing wrong")
        return 1
    cov_bad = decl_bad + check_coverage(rules, declared)
    n_empty = sum(1 for r in rules if r.get("total") == 0)
    print(f"  coverage: {len(rules)} rule(s), {n_empty} over an EMPTY population; "
          f"{len(declared)} level(s) declared unmodelled")

    bad = bad + cov_bad
    for b in bad:
        print(f"  FAIL: {b}")
    print("PASS" if not bad else f"FAIL ({len(bad)} violation(s))")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
