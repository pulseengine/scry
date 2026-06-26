# scry-sai-bits

The pure **known-bits × interval-guarded congruence** reduced-product abstract
domain for [scry](https://github.com/pulseengine/scry) (FEAT-037, DD-017).

A dependency-free crate (the sibling of `scry-sai-interval` / `scry-sai-octagon`)
that captures alignment, low-bit patterns, and induction strides the interval and
octagon domains miss — for alignment-driven bounds-check elision and bit-level
specialization in codegen consumers.

## The two components

* **Known-bits** (`KnownBits`) — LLVM-`KnownBits` style: each bit is *known-0*,
  *known-1*, or *unknown*. `γ(zeros, ones) = { x | x & zeros == 0 ∧ x & ones == ones }`.
* **Congruence** (`Cong`) — Granger's domain `x ≡ r (mod m)`, with `m == 0` the
  singleton `{r}` and `m == 1` the top.

`BitsCong` is the reduced product, with a `reduce` operator that exchanges the
2-adic residue between the two (a fixed low-bit prefix ⇔ `mod 2^k`).

## Soundness over wrapping arithmetic

Wasm integer ops wrap mod `2^w`. A congruence survives a wrapping `add`/`sub`/`mul`
**only when `m | 2^w`**. So a possibly-wrapping transfer weakens the modulus to
`gcd(m, 2^w) = 2^min(v2(m), w)`; the full modulus is retained only when the
caller passes `wrap_free = true` (the analyzer's interval-domain no-wrap proof).
This is what lets a non-power-of-two stride like `i ≡ 2 (mod 3)` survive soundly.

The load-bearing fact — `(x + y) mod 2^w ≡ r1 + r2 (mod gcd(m, 2^w))` — is
mechanized admit-free in `proofs/rocq/BitsCongruence.v`. Every public transfer is
falsified for soundness by the crate's exhaustive γ-sweep tests at `w = 8`
(including the wrapping semantics and all residue classes mod ≤ 12).

## License

Same as the scry workspace.
