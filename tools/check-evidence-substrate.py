#!/usr/bin/env python3
"""scry#215: the evidence and the artifact must be made on the same substrate.

Two skews, both measured on SHIPPED artifacts rather than read off a config:

  * COMPILER. `bazel build //:scry` builds the released component with a PINNED
    rustc; the MC/DC subject (`crates/scry-mcdc`, a separate workspace) was
    built by whatever `dtolnay/rust-toolchain@stable` resolved to that day. The
    pin is not a hypothesis — v3.3.0's signed `scry-3.3.0-wasm32-wasip2.wasm`
    records `processed-by rustc [1.91.1 (ed61e7d7e 2025-11-07)]`, matching
    MODULE.bazel's `versions = ["1.91.1"]`. The floating side has no record at
    all, and the gap widens on its own.

  * TOOL. The MC/DC gate installs witness at rev 6ff96e75 (= tag v0.29.0); the
    release job that produces the RELEASED evidence bundle installs
    `--tag v0.30.0` and runs the compliance action at `@v0.30.0`. Read off the
    artifact: v3.3.0's evidence manifest says `witness_version: "0.30.0"`. So
    the floors were proved by one tool version and the shipped evidence was
    produced by another.

Neither check makes the two binaries identical — they cannot be (wasip1 core
module with DWARF vs wasip2 component, deliberately; see
crates/scry-mcdc/Cargo.toml). They remove skew that nothing currently tracks.

WHY SHA-ONLY FOR WITNESS: comparing `--rev 6ff96e75...` against `--tag v0.30.0`
textually cannot work, and resolving a tag needs network access from the gate.
Requiring every reference to be a 40-hex commit makes them comparable offline.
That is the same pinning hygiene scry#232 is adding for third-party actions,
arrived at from the verification side rather than the supply-chain side.

Run with --self-test first; it proves the predicates discriminate in BOTH
directions before they are pointed at the real tree.
"""
import sys, re, os, glob, tempfile

WITNESS_REPO = "pulseengine/witness"
SHA40 = re.compile(r'^[0-9a-f]{40}$')

# `REV=<sha>` / `WITNESS_REV: <sha>` / `WITNESS_VERSION: v0.30.0`
ASSIGN = re.compile(
    r'(?:^|\s)(?:WITNESS_REV|WITNESS_VERSION|REV)\s*[:=]\s*"?([A-Za-z0-9._-]+)"?',
    re.M)
# `uses: pulseengine/witness/...@<ref>`
USES = re.compile(r'uses:\s*' + re.escape(WITNESS_REPO) + r'(?:/[^@\s]*)?@([A-Za-z0-9._-]+)')
# A bare 40-hex on a line that also mentions witness — e.g. the binary cache
# key `key: witness-bins-${{ runner.os }}-6ff96e75...`. This one is the
# nastiest of the lot: bump the install rev and forget the cache key, and the
# cache serves the OLD binaries while the install step advertises the new rev.
# The gate would then report coverage from a witness it does not pin, which is
# the same wrong-substrate error one level down.
BARE_SHA = re.compile(r'(?<![0-9a-f])([0-9a-f]{40})(?![0-9a-f])')


def witness_refs(workflow_dir=".github/workflows"):
    """-> [(file, lineno, ref)] for every witness version named in a workflow."""
    found = []
    for path in sorted(glob.glob(os.path.join(workflow_dir, "*.yml"))):
        text = open(path, encoding="utf-8").read()
        mentions_witness = WITNESS_REPO in text or "witness-mcdc" in text
        for i, line in enumerate(text.splitlines(), 1):
            for m in USES.finditer(line):
                found.append((path, i, m.group(1)))
            if not mentions_witness:
                continue
            matched = False
            for m in ASSIGN.finditer(line):
                found.append((path, i, m.group(1)))
                matched = True
            # Only scan for bare SHAs on lines that name witness themselves,
            # so an unrelated commit hash elsewhere is not dragged in.
            if not matched and "witness" in line.lower():
                for m in BARE_SHA.finditer(line):
                    found.append((path, i, m.group(1)))
    return found


def bazel_rustc(path="MODULE.bazel"):
    """The rustc the SHIPPED component is built with."""
    text = open(path, encoding="utf-8").read()
    m = re.search(r'rust\.toolchain\((.*?)\)', text, re.S)
    if not m:
        return None
    v = re.search(r'versions\s*=\s*\[\s*"([^"]+)"', m.group(1))
    return v.group(1) if v else None


def mcdc_rustc(path="crates/scry-mcdc/rust-toolchain.toml"):
    """The rustc the MC/DC SUBJECT is built with, or None if it floats."""
    if not os.path.isfile(path):
        return None
    text = open(path, encoding="utf-8").read()
    m = re.search(r'^\s*channel\s*=\s*"([^"]+)"', text, re.M)
    return m.group(1) if m else None


# ── Known-open skews ────────────────────────────────────────────────────
# A skew listed here is REPORTED, not failed — so this check can be wired
# into a REQUIRED job today while one half is still open. Every entry names
# the issue that owns it.
#
# The entries are self-cleaning, and that is the point: if a listed skew is
# no longer present, this check FAILS and tells you to delete the entry. So
# the allowlist cannot quietly outlive the defect, and a stale entry is a
# live regression test of the checker itself — the one shape in this repo's
# vacuous-gate history that works in your favour.
EXPECTED_SKEWS = {
    "witness-version":
        "scry#215 — the MC/DC gate proves the floors with witness v0.29.0 "
        "(rev 6ff96e75) while the RELEASED evidence bundle is produced by "
        "v0.30.0 (both the `cargo install --tag` and the compliance action, "
        "which are coherent with each other). Converging them changes either "
        "what proved the floors or an unsimulated release path, so the "
        "direction is a deliberate decision and not this change.",
}


def verdict(refs, bazel_v, mcdc_v, expected=None):
    """-> (fails, reported). `fails` blocks; `reported` is known-open.

    A skew in `expected` moves from `fails` to `reported`. An `expected` key
    whose skew is ABSENT becomes a failure, so the allowlist self-cleans."""
    if expected is None:
        expected = EXPECTED_SKEWS
    fails, reported, seen = [], [], set()

    def skew(key, msg):
        seen.add(key)
        if key in expected:
            reported.append((key, msg, expected[key]))
        else:
            fails.append(msg)

    # ── tool: every witness reference is one identical 40-hex commit ──
    non_sha = [(f, n, r) for (f, n, r) in refs if not SHA40.match(r)]
    distinct = sorted({r for (_, _, r) in refs})
    if non_sha or len(distinct) > 1:
        by_ref = {}
        for f, n, r in refs:
            by_ref.setdefault(r, []).append(f"{f}:{n}")
        detail = "\n".join(f"      {r}{'  (not a 40-hex commit)' if not SHA40.match(r) else ''}"
                            f"  <- {', '.join(sites)}"
                            for r, sites in sorted(by_ref.items()))
        skew("witness-version",
             f"witness is pinned {len(distinct)} different way(s); the gate that proves "
             "the MC/DC floors and the job that produces the RELEASED evidence must be "
             "the same tool, and every reference must be a 40-hex commit so they can "
             f"be compared without network access:\n{detail}")
    if not refs:
        # Never allowlistable: losing the subject is how a gate goes vacuous.
        fails.append("no witness reference found at all — this check has lost its subject")

    # ── compiler: the MC/DC subject matches the shipped artifact's rustc ──
    if bazel_v is None:
        fails.append("could not read rust.toolchain versions from MODULE.bazel")
    elif mcdc_v is None:
        skew("mcdc-rustc",
             "crates/scry-mcdc has no rust-toolchain.toml, so the MC/DC subject is "
             f"built by whatever @stable resolves to, while the shipped component is "
             f"built with rustc {bazel_v}")
    elif mcdc_v != bazel_v:
        skew("mcdc-rustc",
             f"MC/DC subject pins rustc {mcdc_v} but the shipped component is built "
             f"with {bazel_v} (MODULE.bazel)")

    # Self-cleaning: an allowlisted skew that is no longer present must go.
    for key in sorted(set(expected) - seen):
        fails.append(
            f"STALE allowlist entry '{key}': this skew is no longer present, so the "
            f"entry in EXPECTED_SKEWS is now hiding nothing and must be deleted. "
            f"It was recorded as: {expected[key]}")
    return fails, reported


def self_test():
    ok = True
    S1 = "a" * 40
    S2 = "b" * 40
    NO_ALLOW = {}
    ALLOW_W = {"witness-version": "owned by scry#215"}

    # (label, refs, bazel, mcdc, allowlist, expect_block)
    cases = [
        # ── aligned: nothing to say ─────────────────────────────────────
        ("aligned, empty allowlist",
         [("ci", 1, S1), ("rel", 2, S1)], "1.91.1", "1.91.1", NO_ALLOW, False),
        # ── unexpected skews BLOCK ──────────────────────────────────────
        ("two different SHAs, not allowlisted",
         [("ci", 1, S1), ("rel", 2, S2)], "1.91.1", "1.91.1", NO_ALLOW, True),
        ("a tag instead of a SHA, not allowlisted",
         [("ci", 1, S1), ("rel", 2, "v0.30.0")], "1.91.1", "1.91.1", NO_ALLOW, True),
        ("floating mcdc toolchain, not allowlisted",
         [("ci", 1, S1)], "1.91.1", None, NO_ALLOW, True),
        ("mcdc toolchain disagrees with Bazel",
         [("ci", 1, S1)], "1.91.1", "1.99.0", NO_ALLOW, True),
        # ── allowlisted skews REPORT, do not block ──────────────────────
        ("today's real shape: witness skew allowlisted, rustc aligned",
         [("ci", 1, S1), ("rel", 2, S1), ("rel", 3, "v0.30.0")],
         "1.91.1", "1.91.1", ALLOW_W, False),
        # ── the allowlist must NOT cover a different skew ────────────────
        ("witness allowlisted does not excuse a floating toolchain",
         [("ci", 1, S1), ("rel", 2, "v0.30.0")], "1.91.1", None, ALLOW_W, True),
        # ── SELF-CLEANING: a stale entry blocks ─────────────────────────
        ("stale entry: witness now aligned but still allowlisted",
         [("ci", 1, S1), ("rel", 2, S1)], "1.91.1", "1.91.1", ALLOW_W, True),
        # ── losing the subject is never allowlistable ───────────────────
        ("no witness reference at all, even with the allowlist",
         [], "1.91.1", "1.91.1", ALLOW_W, True),
        ("MODULE.bazel unreadable is never allowlistable",
         [("ci", 1, S1)], None, "1.91.1", ALLOW_W, True),
        # ── Added after a mutation check. Both of these SURVIVED first: ──
        # M3 (SHA40 accepts anything): the tag case above also had two
        # DIFFERENT refs, so `len(distinct) > 1` blocked it whether the regex
        # worked or not. The regex was never load-bearing. This row makes every
        # ref an IDENTICAL tag — textually comparable, still unresolvable
        # without network — so only the regex can catch it.
        ("every ref is the same TAG: comparable, but not offline",
         [("ci", 1, "v0.30.0"), ("rel", 2, "v0.30.0")],
         "1.91.1", "1.91.1", NO_ALLOW, True),
        # M5 (lost subject becomes allowlistable): the no-refs case above
        # allowlisted `witness-version`, not `no-refs`, so the mutation was
        # never tested by its own key. Losing the subject must be unallowlistable
        # even when someone names it explicitly.
        ("lost subject is not allowlistable even by its own key",
         [], "1.91.1", "1.91.1", {"no-refs": "someone tried to silence this"}, True),
    ]
    for label, refs, bv, mv, allow, expect_block in cases:
        fails, _ = verdict(refs, bv, mv, allow)
        got_block = bool(fails)
        if got_block != expect_block:
            print(f"  SELF-TEST FAIL ({label}): "
                  f"{'blocked' if got_block else 'passed'}, expected "
                  f"{'block' if expect_block else 'pass'}")
            ok = False

    # An allowlisted skew must be REPORTED, not silently dropped.
    fails, reported = verdict(
        [("ci", 1, S1), ("rel", 2, "v0.30.0")], "1.91.1", "1.91.1", ALLOW_W)
    if fails or [k for k, _, _ in reported] != ["witness-version"]:
        print(f"  SELF-TEST FAIL: allowlisted skew not reported: "
              f"fails={len(fails)} reported={[k for k,_,_ in reported]}")
        ok = False

    # Both outcomes present, or the table passes against a constant predicate.
    if not (any(c[5] for c in cases) and any(not c[5] for c in cases)):
        print("  SELF-TEST FAIL: table does not exercise both outcomes"); ok = False

    # The parser must find the real tree's refs, or every predicate above is
    # being fed an empty list in production.
    real = witness_refs()
    if len(real) < 5:
        print(f"  SELF-TEST FAIL: parser found {len(real)} witness refs in "
              f".github/workflows, expected at least 5 (ci.yml REV + its cache "
              f"key, release.yml WITNESS_VERSION + the compliance action + "
              f"WITNESS_REV)"); ok = False
    # ── the PARSER, against synthetic workflow text ──────────────────
    # Everything above feeds `verdict` pre-built tuples, so none of it
    # exercises witness_refs(). Added after a mutation check: dropping the
    # `"witness" in line` guard from the bare-SHA scan SURVIVED, because no
    # unrelated 40-hex string exists in the workflows TODAY. scry#232 is
    # pinning every GitHub Action to a commit SHA, so the day it lands there
    # will be dozens, and an unguarded scan would report them as conflicting
    # witness versions and fail CI for no reason.
    with tempfile.TemporaryDirectory() as td:
        OTHER = "c" * 40
        WIT = "d" * 40
        open(os.path.join(td, "probe.yml"), "w", encoding="utf-8").write(
            "jobs:\n"
            "  j:\n"
            "    steps:\n"
            f"      - uses: actions/checkout@{OTHER}\n"
            "      - uses: Swatinem/rust-cache@v2\n"
            "      - name: Cache build\n"
            "        uses: actions/cache@v4\n"
            "        with:\n"
            f"          key: build-cache-${{{{ runner.os }}}}-{OTHER}\n"
            "      - name: Cache witness binaries\n"
            "        uses: actions/cache@v4\n"
            "        with:\n"
            f"          key: witness-bins-${{{{ runner.os }}}}-{WIT}\n"
            "      - run: |\n"
            f"          REV={WIT}\n"
            "          cargo install --git $URL --rev \"$REV\" witness-mcdc\n")
        got = sorted({r for _, _, r in witness_refs(td)})
        if got != [WIT]:
            print(f"  SELF-TEST FAIL (parser): picked up {got}, expected only "
                  f"the witness ref {WIT!r}. A non-witness action or cache key "
                  f"pinned to a SHA must NOT be read as a witness version "
                  f"(scry#232 pins every action to a SHA).")
            ok = False

    # The binary cache key is a BARE sha on a witness line, not a VAR=
    # assignment, so only the bare-SHA scan reaches it. If that scan
    # regresses, this row notices — and the hazard it guards is specific:
    # bumping the install rev while the cache key keeps the old one makes the
    # cache serve binaries the install step no longer names.
    cache_key_refs = [
        (f, n) for f, n, _ in real
        if open(f, encoding="utf-8").read().splitlines()[n - 1].lstrip().startswith("key:")
    ]
    if len(cache_key_refs) < 2:
        print(f"  SELF-TEST FAIL: bare-SHA scan found {len(cache_key_refs)} witness "
              f"cache-key refs, expected 2 (ci.yml and release.yml both cache the "
              f"built binaries keyed by rev)"); ok = False

    print("  self-test:", "OK — blocks, reports and self-cleans" if ok else "FAILED")
    return 0 if ok else 1


def main():
    if "--self-test" in sys.argv:
        return self_test()
    refs = witness_refs()
    bazel_v = bazel_rustc()
    mcdc_v = mcdc_rustc()
    fails, reported = verdict(refs, bazel_v, mcdc_v)

    print(f"  shipped component rustc : {bazel_v}  (MODULE.bazel; v3.3.0's signed "
          f"wasm records `processed-by rustc [1.91.1 ...]`)")
    print(f"  MC/DC subject rustc     : {mcdc_v or 'FLOATING (@stable)'}")
    print(f"  witness references      : {len(refs)} across "
          f"{len({f for f, _, _ in refs})} workflow file(s)")
    for f, n, r in refs:
        print(f"      {f}:{n}  {r}")

    for key, msg, why in reported:
        print(f"\n::notice title=scry#215 known-open substrate skew "
              f"({key})::{msg}\n    OWNED BY: {why}")
    if fails:
        for msg in fails:
            print(f"\n::error title=scry#215 evidence substrate::{msg}")
        print(f"\n  FAILED — {len(fails)} unexpected or stale substrate skew(s)")
        return 1
    if reported:
        print(f"\n  OK — {len(reported)} known-open skew(s), each owned by an issue; "
              f"nothing unexpected, nothing stale")
    else:
        print("\n  OK — evidence and artifact share a compiler, and one witness commit")
    return 0


if __name__ == "__main__":
    sys.exit(main())
