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
"""
import sys, re, yaml

PKG = re.compile(r'(?:-p|--package)\s+([A-Za-z0-9_-]+)')


def packages_by_tool(workflow_text):
    """-> {"cargo test": {names}, "cargo clippy": {names}} from a workflow's steps."""
    wf = yaml.safe_load(workflow_text)
    out = {"cargo test": set(), "cargo clippy": set()}
    for job in (wf.get("jobs") or {}).values():
        for step in (job.get("steps") or []):
            run = step.get("run")
            if not run:
                continue
            # A step's run block may contain several commands; attribute each
            # LINE (with continuations joined) to the tool it invokes.
            joined = run.replace("\\\n", " ")
            for line in joined.splitlines():
                for tool in out:
                    if tool in line:
                        out[tool].update(PKG.findall(line))
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
