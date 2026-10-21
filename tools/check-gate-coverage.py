#!/usr/bin/env python3
"""scry#157: assert every publishable crate is covered by BOTH per-package gates.

Parses the workflow as YAML and inspects each step's `run` block, rather than
scraping the file with grep/awk ranges. Three earlier attempts at this check
used text ranges and were vacuous in ways that looked like they worked:

  * a per-crate dynamic regex that survived BSD grep and not GNU grep;
  * an `awk '/cargo test/,/^      - name:/'` range that chained across the whole
    file, so the "tested" and "clippy" lists came out IDENTICAL — the check
    could not detect the very drift it exists for;
  * (elsewhere) a predicate that counted a comment as a gate.

A gate that cannot distinguish its two inputs is worse than no gate, so this one
is exercised by `--self-test` against synthetic good and bad inputs.

scry#208: THE YAML REWRITE REINTRODUCED THE THIRD BUG IT LISTS ABOVE. Matching
was `if tool in line`, a bare substring test, so all three of these counted as
coverage — verified by execution before the fix:

    # cargo test -p a -p b                    (a comment)
    cargo test -p a  /  continue-on-error     (a step that cannot fail)
    echo "run cargo test -p a before pushing" (the name inside a string)

The last one was not in the issue; it turned up writing the red-first case for
the other two. The common shape is that the matcher asked "does this text appear
somewhere on the line" when the question is "does this line RUN the tool".

So matching now (a) strips shell comments, (b) requires the tool at the START of
a command segment — splitting on &&, ||, ; and | and skipping leading VAR=value
assignments and a `cargo +toolchain` selector — and (c) ignores any step or job
carrying `continue-on-error: true`, because a step that cannot fail is not a
gate (scry#207 is the same defect one level up, on the proof jobs).
"""
import sys, re, yaml

PKG = re.compile(r'(?:-p|--package)\s+([A-Za-z0-9_-]+)')
# A `#` starts a shell comment only at a word boundary, so `foo#bar` survives.
COMMENT = re.compile(r'(?:^|\s)#.*$')
ENV_ASSIGN = re.compile(r'^[A-Za-z_][A-Za-z0-9_]*=\S*\s+')
SEGMENT_SEP = re.compile(r'&&|\|\||;|\|')


def command_segments(line):
    """Yield the commands a shell line would actually execute."""
    line = COMMENT.sub("", line)
    for seg in SEGMENT_SEP.split(line):
        seg = seg.strip()
        # `FOO=1 BAR=2 cargo test ...` runs cargo, not FOO.
        while True:
            m = ENV_ASSIGN.match(seg)
            if not m:
                break
            seg = seg[m.end():]
        if seg:
            yield seg


def invokes(segment, tool):
    """True iff `segment` RUNS `tool` (e.g. "cargo test"), rather than merely
    mentioning it. `cargo +1.99.0 test` counts; `echo cargo test` does not."""
    toks = segment.split()
    if len(toks) >= 2 and toks[1].startswith("+"):
        toks = [toks[0]] + toks[2:]
    return len(toks) >= 2 and f"{toks[0]} {toks[1]}" == tool


def packages_by_tool(workflow_text):
    """-> {"cargo test": {names}, "cargo clippy": {names}} from a workflow's steps."""
    wf = yaml.safe_load(workflow_text)
    out = {"cargo test": set(), "cargo clippy": set()}
    for job in (wf.get("jobs") or {}).values():
        if job.get("continue-on-error"):
            continue  # scry#207/#208: a job that cannot fail is not a gate
        for step in (job.get("steps") or []):
            if step.get("continue-on-error"):
                continue
            run = step.get("run")
            if not run:
                continue
            # A step's run block may contain several commands; attribute each
            # LINE (with continuations joined) to the tool it invokes.
            joined = run.replace("\\\n", " ")
            for line in joined.splitlines():
                for segment in command_segments(line):
                    for tool in out:
                        if invokes(segment, tool):
                            out[tool].update(PKG.findall(segment))
    return out


def publishable_crates(root="crates"):
    import os
    names = []
    for d in sorted(os.listdir(root)):
        p = os.path.join(root, d, "Cargo.toml")
        if not os.path.isfile(p):
            continue
        txt = open(p).read()
        if re.search(r'^publish\s*=\s*false', txt, re.M):
            continue
        m = re.search(r'^name\s*=\s*"([^"]+)"', txt, re.M)
        if m:
            names.append(m.group(1))
    return names


def self_test():
    good = """
jobs:
  t:
    steps:
      - run: cargo test -p a -p b
      - run: cargo clippy -p a -p b --all-targets -- -D warnings
"""
    bad = """
jobs:
  t:
    steps:
      - run: cargo test -p a -p b
      - run: cargo clippy -p a --all-targets -- -D warnings
"""
    g = packages_by_tool(good)
    b = packages_by_tool(bad)
    ok = True
    if g["cargo test"] != {"a", "b"} or g["cargo clippy"] != {"a", "b"}:
        print(f"  SELF-TEST FAIL (good): {g}"); ok = False
    if b["cargo clippy"] != {"a"}:
        print(f"  SELF-TEST FAIL (bad, clippy): {b}"); ok = False
    if b["cargo test"] != {"a", "b"}:
        print(f"  SELF-TEST FAIL (bad, test): {b}"); ok = False
    # The property that matters: the two tools must be DISTINGUISHABLE.
    if b["cargo test"] == b["cargo clippy"]:
        print("  SELF-TEST FAIL: the two gates are indistinguishable — vacuous"); ok = False

    # scry#208: text that MENTIONS the tool must not count as RUNNING it.
    # Each of these credited {a, b} before the fix. The old self-test fed the
    # matcher only inputs its author already believed it handled, which is the
    # recurring shape in this repo's vacuous-gate findings — so these are the
    # cases that were missing, not extra ones.
    mentions_only = [
        ("a comment", """
jobs:
  t:
    steps:
      - run: |
          # cargo test -p a -p b
          # cargo clippy -p a -p b --all-targets -- -D warnings
          echo "the real invocations are gone"
"""),
        ("a step that cannot fail", """
jobs:
  t:
    steps:
      - run: cargo test -p a -p b
        continue-on-error: true
      - run: cargo clippy -p a -p b
        continue-on-error: true
"""),
        ("a job that cannot fail", """
jobs:
  t:
    continue-on-error: true
    steps:
      - run: cargo test -p a -p b
      - run: cargo clippy -p a -p b
"""),
        ("the name inside a string", """
jobs:
  t:
    steps:
      - run: echo "remember to run cargo test -p a -p b before pushing"
"""),
        # Added after a mutation check: deleting the comment-stripping line
        # SURVIVED the four cases above, because requiring the tool at the
        # start of a segment already rejects a line beginning with `#`. The
        # two defences overlap, and nothing exercised the gap — a comment
        # carrying a shell SEPARATOR, which splits into a segment that does
        # start with the tool.
        ("a comment containing a separator", """
jobs:
  t:
    steps:
      - run: |
          cargo build --workspace  # or: cargo test -p a || cargo test -p b
"""),

    ]
    for label, text in mentions_only:
        m = packages_by_tool(text)
        if m["cargo test"] or m["cargo clippy"]:
            print(f"  SELF-TEST FAIL (scry#208, {label}): credited {m}"); ok = False

    # And the other direction, or the fix above would pass by rejecting
    # everything: forms that DO run the tool must still be credited.
    runs_it = [
        ("plain", "cargo test -p a -p b", {"a", "b"}),
        ("env prefix", "RUSTFLAGS=-Dwarnings CARGO_TERM_COLOR=always cargo test -p a -p b", {"a", "b"}),
        ("pinned toolchain", "cargo +1.99.0 test -p a -p b", {"a", "b"}),
        ("chained after another command", "mkdir -p out && cargo test -p a -p b", {"a", "b"}),
        ("piped", "cargo test -p a -p b 2>&1 | tee log", {"a", "b"}),
        # Same mutation, the other way: a package named only in a trailing
        # comment must not be harvested by PKG.findall.
    ]

    # Same mutation, the opposite direction, and it needs a BLOCK scalar: in a
    # plain `run: cmd  # note` YAML eats the comment before this script sees it,
    # so a shell comment only reaches the matcher inside `run: |`. A package
    # named only in such a comment must not be harvested by PKG.findall.
    commented_pkg = packages_by_tool("""
jobs:
  t:
    steps:
      - run: |
          cargo test -p a  # not -p b yet
""")
    if commented_pkg["cargo test"] != {"a"}:
        print(f"  SELF-TEST FAIL (scry#208, package named in a trailing comment): "
              f"got {commented_pkg['cargo test']}, want {{'a'}}")
        ok = False
    for label, cmd, expect in runs_it:
        text = "jobs:\n  t:\n    steps:\n      - run: " + cmd + "\n"
        m = packages_by_tool(text)
        if m["cargo test"] != expect:
            print(f"  SELF-TEST FAIL (scry#208, {label} should COUNT): got {m['cargo test']}, want {expect}")
            ok = False

    print("  self-test:", "OK — good input clean, bad input detected" if ok else "FAILED")
    return 0 if ok else 1


def main():
    if "--self-test" in sys.argv:
        return self_test()
    wf = sys.argv[1] if len(sys.argv) > 1 else ".github/workflows/ci.yml"
    by = packages_by_tool(open(wf).read())
    missing = []
    for name in publishable_crates():
        for tool in ("cargo test", "cargo clippy"):
            if name not in by[tool]:
                missing.append(f"{name}({tool.split()[1]})")
    if missing:
        print("::error::publishable crate(s) missing from a gate: " + " ".join(missing))
        return 1
    print(f"OK — {len(publishable_crates())} publishable crates in BOTH gates")
    return 0


if __name__ == "__main__":
    sys.exit(main())
