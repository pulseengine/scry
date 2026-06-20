# scry-sai-octagon

The **octagon relational abstract domain** for
[scry](https://github.com/pulseengine/scry) (Miné, HOSC 2006). Part of the
`scry-sai-*` (Sound Abstract Interpretation) family.

A pure, `#![no_std]`, dependency-free Difference-Bound-Matrix implementation of
constraints `±x ± y ≤ c`: `close` (Floyd–Warshall) and `strong_close` (Miné
tight closure), `join`/`meet`/`widen`/`narrow`/`leq`, plus the analyzer-facing
transfers — `forget` (sound havoc on write), `assign_const`/`assign_copy`/
`assign_add_const` (incl. the in-place increment that carries a relation across
a loop), `add_diff`/`set_upper`/`set_lower`, and `bound_of` (project a variable
to an integer interval). All arithmetic is saturating and INF-absorbing.

scry carries this domain alongside intervals through its loop fixpoint, so a
counter bounded by a *variable* relation (`i < n`) stays bounded. Falsified by
γ-sweep tests against the concrete semantics. Imported as `scry_octagon`.

License: MIT OR Apache-2.0.
