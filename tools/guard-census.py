#!/usr/bin/env python3
"""Guard-shape census over a flat WAT dump (FEAT-098 AC#4 evidence).

WHY. FEAT-098 was filed on the claim that LLVM's bounds checks are the
constant-operand `local.get x; i32.const c; i32.lt_u; br_if` shape scry
declined to read. The measured delta on scry_mcdc.wasm was zero, and the
reason is a CORPUS fact: the two-local form (`x <u y`) outnumbers the
constant form. That number is cited on the artifact, so it must be
re-derivable rather than trusted:

    wasm-tools strip module.wasm -o stripped.wasm
    wasm-tools print stripped.wasm > module.wat
    python3 tools/guard-census.py module.wat

It counts 4-instruction windows `local.get|local.tee; (i32.const c |
local.get y); <i32 cmp>; br_if|if`, split by operand shape, signedness and
terminator, and splits the unsigned constant guards by FEAT-098's side
condition (c <= 2^31 as u32). It is a text-level census of syntactic
shapes, not an analysis: it does not know which guards sit in degraded
functions or which ones the analyzer's own peephole actually matched.
"""
import collections
import sys


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit("usage: guard-census.py <flat.wat>")
    lines = [ln.strip() for ln in open(sys.argv[1], encoding="utf-8")]
    cmp_u = {"i32.lt_u", "i32.gt_u", "i32.le_u", "i32.ge_u"}
    cmp_s = {"i32.lt_s", "i32.gt_s", "i32.le_s", "i32.ge_s", "i32.eq", "i32.ne"}
    shapes: collections.Counter = collections.Counter()
    consts: collections.Counter = collections.Counter()
    for i in range(len(lines) - 3):
        a, b, c, d = lines[i], lines[i + 1], lines[i + 2], lines[i + 3]
        if not (a.startswith("local.get") or a.startswith("local.tee")):
            continue
        if d.startswith("br_if"):
            term = "br_if"
        elif d.startswith("if"):
            term = "if"
        else:
            continue
        op = c.split()[0] if c else ""
        if op in cmp_u:
            fam = "unsigned"
        elif op in cmp_s:
            fam = "signed/eq"
        else:
            continue
        if b.startswith("i32.const"):
            shape = "const"
            if fam == "unsigned":
                u = int(b.split()[1]) & 0xFFFFFFFF
                consts["c<=2^31" if u <= 2**31 else "c>2^31"] += 1
        elif b.startswith("local.get"):
            shape = "two-local"
        else:
            continue
        shapes[(shape, fam, term)] += 1
    for key in sorted(shapes):
        print(f"{key[0]:<10} {key[1]:<10} ...; {key[2]:<6} : {shapes[key]}")
    print("unsigned const guards by side condition:", dict(consts))
    print("total br_if lines:", sum(1 for ln in lines if ln.startswith("br_if")))
    print("total if lines   :", sum(1 for ln in lines if ln.startswith("if")))


if __name__ == "__main__":
    main()
