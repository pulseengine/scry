#!/usr/bin/env python3
"""Gate: no artifact may depend on one scheduled for a LATER release.

WHY. v3.3.0's FEAT-064 is satisfiable only via FEAT-077 and FEAT-087, both
v3.4.0 and both already shipped; FEAT-069 depends on FEAT-095 (v3.5.0). So
v3.3.0 CANNOT BE CUT BEFORE v3.4.0, and no amount of work on its other items
changes that -- the dependency runs the wrong way across the release boundary.

Anyone reading "v3.3.0: 3 proposed" assumes three pieces of work remain. Two of
them are ORDERING, not work. A release plan is a snapshot of what you believed
when you wrote it, and nothing re-checks it when the belief changes -- so this
does.

THE ALLOWLIST IS THE POINT, not an escape hatch. Three inversions exist today.
Failing on them would put main red for a condition that is real, understood, and
recorded (scry#187) -- so they are listed here WITH their reason, and anything
NEW fails. A known problem that must be re-acknowledged to stay known is the
opposite of a suppressed one: removing an entry here is how you record that an
inversion was resolved.

AND THE ALLOWLIST GUARDS THE CHECKER. A stale entry -- one naming an inversion
that is no longer real -- FAILS. So the three known pairs are three facts the
detection logic must keep re-deriving from live artifacts on every run. Flip the
comparison operator and all three go stale and the gate goes red; that mutant was
run. A suppression list you can only ever add to is how gates rot, so this one
costs something to keep.

NOT ENFORCEABLE BEFORE 2026-08-28: FEAT-064's dependency lived in PROSE inside an
acceptance criterion, so no tool could see it. Typed `depends-on` links made it
visible; this makes it checked.
"""
import sys, glob

try:
    import yaml
except ImportError:
    # FAIL CLOSED: a gate that skips on a missing dep reports green while
    # checking nothing (the scry#141 failure mode).
    print("FAIL: PyYAML not available -- this gate cannot run", file=sys.stderr)
    sys.exit(1)

# (dependent, dependency) pairs that are KNOWN and RECORDED. Each needs a reason.
KNOWN = {
    ("FEAT-064", "FEAT-077"): "scry#187 — FEAT-064's AC1 was falsified and repaired in v3.4.0; the plan did not follow the discovery",
    ("FEAT-064", "FEAT-087"): "scry#187 — same repair, second identity bit",
    ("FEAT-069", "FEAT-095"): "the OOB proven rate is blocked on region-havoc coverage, measured at 92.5% of unproven obligations",
}


def release_key(v):
    try:
        return tuple(int(x) for x in str(v).lstrip("v").split("."))
    except Exception:
        return (99, 99, 99)


def collect(docs):
    """-> (release_of, depends_on). Pure: the self-test drives this too."""
    release_of, depends_on = {}, {}
    for d in docs:
        if not isinstance(d, dict):
            continue
        for a in d.get("artifacts") or []:
            if not isinstance(a, dict) or not a.get("id"):
                continue
            if a.get("release"):
                release_of[a["id"]] = a["release"]
            for l in a.get("links") or []:
                if isinstance(l, dict) and l.get("type") == "depends-on":
                    depends_on.setdefault(a["id"], []).append(l.get("target"))
    return release_of, depends_on


def verdict(release_of, depends_on, known=None):
    """-> (new_inversions, known_seen). Only NEW ones are failures."""
    known = KNOWN if known is None else known
    new, seen = [], []
    for src, targets in depends_on.items():
        for tgt in targets:
            if src not in release_of or tgt not in release_of:
                continue
            if release_key(release_of[tgt]) > release_key(release_of[src]):
                item = (src, release_of[src], tgt, release_of[tgt])
                (seen if (src, tgt) in known else new).append(item)
    return new, seen


def self_test():
    R = {"A": "v1.0.0", "B": "v2.0.0", "C": "v1.0.0"}
    cases = [
        ("clean: dependency in an EARLIER release", R, {"B": ["A"]}, {}, 0, 0),
        ("clean: same release", R, {"A": ["C"]}, {}, 0, 0),
        ("NEW inversion fails", R, {"A": ["B"]}, {}, 1, 0),
        ("a KNOWN inversion is allowed but reported", R, {"A": ["B"]}, {("A", "B"): "why"}, 0, 1),
        ("unknown target is ignored, not crashed", R, {"A": ["ZZZ"]}, {}, 0, 0),
        ("two new inversions are both reported", {**R, "D": "v3.0.0"},
         {"A": ["B", "D"]}, {}, 2, 0),
    ]
    bad = 0
    for name, rel, dep, known, wn, wk in cases:
        n, k = verdict(rel, dep, known)
        ok = len(n) == wn and len(k) == wk
        bad += not ok
        print(f"  [{'ok' if ok else 'SELF-TEST FAILED'}] {name}: {len(n)} new / {len(k)} known, "
              f"expected {wn}/{wk}")
    return bad


def main():
    if "--self-test" in sys.argv:
        f = self_test()
        print("SELF-TEST PASS" if not f else f"SELF-TEST FAIL ({f})")
        return 1 if f else 0

    paths = sorted(glob.glob("artifacts/**/*.yaml", recursive=True))
    docs = []
    for p in paths:
        try:
            docs.append(yaml.safe_load(open(p, encoding="utf-8")))
        except Exception as e:
            print(f"FAIL: unparseable {p}: {e}")
            return 1
    release_of, depends_on = collect(docs)
    if not release_of:
        print("FAIL: no artifact carries a release -- the scan found nothing to check")
        return 1
    new, seen = verdict(release_of, depends_on)
    print(f"  scanned {len(paths)} files; {len(release_of)} artifacts carry a release")
    for s, sr, t, tr in sorted(seen):
        print(f"  known: {s} ({sr}) depends-on {t} ({tr}) — {KNOWN[(s, t)]}")
    stale = [k for k in KNOWN if k not in {(s, t) for s, _, t, _ in seen}]
    for s, t in sorted(stale):
        print(f"  FAIL: allowlist entry {s} -> {t} no longer describes a real inversion; "
              f"remove it (that is how a resolved inversion gets recorded)")
    for s, sr, t, tr in sorted(new):
        print(f"  FAIL: {s} ({sr}) depends-on {t} ({tr}) — a release cannot be cut before "
              f"one it depends on. Move one of them, or add it to KNOWN with a reason.")
    bad = len(new) + len(stale)
    print("PASS" if not bad else f"FAIL ({bad})")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
