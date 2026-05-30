//! scry-interval — the pure interval + region-memory abstract domain
//! for scry (FEAT-005 region, FEAT-001 interval; extracted for FEAT-013
//! v1.1).
//!
//! ## Why this crate exists (FEAT-013 / DD-011)
//!
//! Through v1.0 the analyzer reached the interval/region algebra over a
//! WIT cross-component import (`pulseengine:wasm-lattice/domain`). That
//! import is exactly what made the composed `//:scry` a hollow ~4.6 KB
//! shell: wac's `--import-dependencies` leaves the lattice as a
//! *root-level component import*, which wasmtime 45 rejects
//! ("root-level component imports are not supported"), so `analyze()`
//! could never run and analyzer source never reached the shipped binary
//! (the v1.0.1 open finding).
//!
//! v1.1 closes that gap by making the algebra a *crate dependency* of
//! the analyzer instead of a WIT import: this crate holds the interval
//! and region operations as plain Rust, the analyzer calls them
//! directly, and the `import pulseengine:wasm-lattice/domain` line
//! leaves the scry world — so the analyzer component imports only WASI
//! and runs standalone.
//!
//! Same pure-crate-dual-compile pattern as [`scry-octagon`] /
//! [`scry-taint`] / [`scry-provenance`]: `#![no_std]`, zero deps,
//! compiles to `wasm32-wasip2` (linked into the analyzer) AND natively
//! (falsified by `scry-host-tests`). The `wasm-lattice` component keeps
//! delegating its WIT `domain` exports to this crate, so the two-
//! component dogfood (DD-008) still demonstrates cross-component WIT —
//! it is just no longer the analyzer's execution path.
//!
//! The transfer functions are byte-for-byte the ones shipped in
//! `wasm-lattice` through v1.0 (interval soundness mechanized in
//! `proofs/rocq/Soundness.v`; region soundness in `proofs/rocq/
//! Region.v`), so this is a pure relocation, not a behaviour change.

#![cfg_attr(not(test), no_std)]

/// Closed interval over signed 64-bit integers (abstracts i32 and i64
/// Wasm values). Bottom (empty) is any interval with `lo > hi`,
/// canonically `{ lo: 1, hi: 0 }`; top is the full i64 range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Interval {
    pub lo: i64,
    pub hi: i64,
}

/// A pointer abstracted as `(region_id, offset)` — the v0.3 region
/// memory domain. Same `region_id` ⇒ necessarily aliased; different
/// `region_id` ⇒ the lattice is non-relational across them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Region {
    pub region_id: u32,
    pub offset: Interval,
}

/// Bottom (empty) interval — the conventional encoding `{ lo: 1, hi: 0 }`.
pub const BOTTOM: Interval = Interval { lo: 1, hi: 0 };

/// Top interval — the full i64 range.
pub const TOP: Interval = Interval {
    lo: i64::MIN,
    hi: i64::MAX,
};

/// True iff `x` is bottom (empty), i.e. `lo > hi`.
#[inline]
pub fn is_bot(x: Interval) -> bool {
    x.lo > x.hi
}

/// Canonicalise `(lo, hi)` to an interval, collapsing `lo > hi` to BOTTOM.
#[inline]
pub fn canon(lo: i64, hi: i64) -> Interval {
    if lo > hi { BOTTOM } else { Interval { lo, hi } }
}

// ── Interval lattice + transfer functions ──────────────────────────
// Bodies are identical to the v0.1–v1.0 wasm-lattice impl.

pub fn bottom() -> Interval {
    BOTTOM
}

pub fn top() -> Interval {
    TOP
}

pub fn is_bottom(x: Interval) -> bool {
    is_bot(x)
}

pub fn leq(a: Interval, b: Interval) -> bool {
    if is_bot(a) {
        return true;
    }
    if is_bot(b) {
        return false;
    }
    b.lo <= a.lo && a.hi <= b.hi
}

pub fn join(a: Interval, b: Interval) -> Interval {
    if is_bot(a) {
        return b;
    }
    if is_bot(b) {
        return a;
    }
    Interval {
        lo: a.lo.min(b.lo),
        hi: a.hi.max(b.hi),
    }
}

pub fn meet(a: Interval, b: Interval) -> Interval {
    if is_bot(a) || is_bot(b) {
        return BOTTOM;
    }
    canon(a.lo.max(b.lo), a.hi.min(b.hi))
}

pub fn widen(a: Interval, b: Interval) -> Interval {
    if is_bot(a) {
        return b;
    }
    if is_bot(b) {
        return a;
    }
    let lo = if b.lo < a.lo { i64::MIN } else { a.lo };
    let hi = if b.hi > a.hi { i64::MAX } else { a.hi };
    Interval { lo, hi }
}

pub fn constant_i32(c: i32) -> Interval {
    Interval {
        lo: c as i64,
        hi: c as i64,
    }
}

pub fn constant_i64(c: i64) -> Interval {
    Interval { lo: c, hi: c }
}

pub fn i32_add(a: Interval, b: Interval) -> Interval {
    if is_bot(a) || is_bot(b) {
        return BOTTOM;
    }
    let lo = a.lo.saturating_add(b.lo);
    let hi = a.hi.saturating_add(b.hi);
    if lo < i32::MIN as i64 || hi > i32::MAX as i64 {
        TOP
    } else {
        Interval { lo, hi }
    }
}

pub fn i32_sub(a: Interval, b: Interval) -> Interval {
    if is_bot(a) || is_bot(b) {
        return BOTTOM;
    }
    let lo = a.lo.saturating_sub(b.hi);
    let hi = a.hi.saturating_sub(b.lo);
    if lo < i32::MIN as i64 || hi > i32::MAX as i64 {
        TOP
    } else {
        Interval { lo, hi }
    }
}

pub fn i32_mul(a: Interval, b: Interval) -> Interval {
    if is_bot(a) || is_bot(b) {
        return BOTTOM;
    }
    let corners = [
        a.lo.saturating_mul(b.lo),
        a.lo.saturating_mul(b.hi),
        a.hi.saturating_mul(b.lo),
        a.hi.saturating_mul(b.hi),
    ];
    let lo = corners.iter().copied().min().unwrap();
    let hi = corners.iter().copied().max().unwrap();
    if lo < i32::MIN as i64 || hi > i32::MAX as i64 {
        TOP
    } else {
        Interval { lo, hi }
    }
}

// ── Region-memory domain (FEAT-005) ─────────────────────────────────

pub fn region_create(region_id: u32) -> Region {
    Region {
        region_id,
        offset: Interval { lo: 0, hi: 0 },
    }
}

pub fn region_offset(r: Region, delta: Interval) -> Region {
    if is_bot(r.offset) || is_bot(delta) {
        return Region {
            region_id: r.region_id,
            offset: BOTTOM,
        };
    }
    let lo = r.offset.lo.saturating_add(delta.lo);
    let hi = r.offset.hi.saturating_add(delta.hi);
    Region {
        region_id: r.region_id,
        offset: canon(lo, hi),
    }
}

pub fn region_leq(a: Region, b: Region) -> bool {
    if a.region_id != b.region_id {
        return is_bot(a.offset);
    }
    if is_bot(a.offset) {
        return true;
    }
    if is_bot(b.offset) {
        return false;
    }
    b.offset.lo <= a.offset.lo && a.offset.hi <= b.offset.hi
}

pub fn region_join(a: Region, b: Region) -> Region {
    if a.region_id != b.region_id {
        return Region {
            region_id: a.region_id,
            offset: TOP,
        };
    }
    let off = if is_bot(a.offset) {
        b.offset
    } else if is_bot(b.offset) {
        a.offset
    } else {
        Interval {
            lo: a.offset.lo.min(b.offset.lo),
            hi: a.offset.hi.max(b.offset.hi),
        }
    };
    Region {
        region_id: a.region_id,
        offset: off,
    }
}

pub fn region_meet(a: Region, b: Region) -> Region {
    if a.region_id != b.region_id {
        return Region {
            region_id: a.region_id,
            offset: BOTTOM,
        };
    }
    let off = if is_bot(a.offset) || is_bot(b.offset) {
        BOTTOM
    } else {
        canon(a.offset.lo.max(b.offset.lo), a.offset.hi.min(b.offset.hi))
    };
    Region {
        region_id: a.region_id,
        offset: off,
    }
}

pub fn region_widen(a: Region, b: Region) -> Region {
    if a.region_id != b.region_id {
        return Region {
            region_id: a.region_id,
            offset: TOP,
        };
    }
    let off = if is_bot(a.offset) {
        b.offset
    } else if is_bot(b.offset) {
        a.offset
    } else {
        let lo = if b.offset.lo < a.offset.lo {
            i64::MIN
        } else {
            a.offset.lo
        };
        let hi = if b.offset.hi > a.offset.hi {
            i64::MAX
        } else {
            a.offset.hi
        };
        Interval { lo, hi }
    };
    Region {
        region_id: a.region_id,
        offset: off,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// γ: does concrete `z` lie in the interval?
    fn gamma(a: Interval, z: i64) -> bool {
        !is_bot(a) && a.lo <= z && z <= a.hi
    }

    #[test]
    fn extrema() {
        assert!(is_bot(BOTTOM));
        assert!(!is_bot(TOP));
        assert!(gamma(TOP, 0));
        assert!(gamma(TOP, i64::MAX));
        assert!(!gamma(BOTTOM, 0));
    }

    #[test]
    fn constants_are_singletons() {
        assert_eq!(constant_i32(42), Interval { lo: 42, hi: 42 });
        assert_eq!(constant_i64(-7), Interval { lo: -7, hi: -7 });
    }

    /// add soundness: za∈γ(a), zb∈γ(b) ⇒ za+zb ∈ γ(a⊞b), over a sweep.
    #[test]
    fn i32_add_is_sound() {
        for alo in -8..=8 {
            for ahi in alo..=8 {
                for blo in -8..=8 {
                    for bhi in blo..=8 {
                        let a = Interval { lo: alo, hi: ahi };
                        let b = Interval { lo: blo, hi: bhi };
                        let r = i32_add(a, b);
                        for za in alo..=ahi {
                            for zb in blo..=bhi {
                                assert!(gamma(r, za + zb), "{a:?}+{b:?} missed {}", za + zb);
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn join_is_upper_bound() {
        let a = Interval { lo: 1, hi: 3 };
        let b = Interval { lo: 7, hi: 9 };
        let j = join(a, b);
        assert!(leq(a, j) && leq(b, j));
        assert!(gamma(j, 1) && gamma(j, 9));
    }

    #[test]
    fn widen_terminates_upward() {
        let a = Interval { lo: 0, hi: 3 };
        let b = Interval { lo: 0, hi: 5 };
        // hi grew → widen to +∞.
        assert_eq!(widen(a, b).hi, i64::MAX);
        // stable → unchanged.
        assert_eq!(widen(a, a), a);
    }

    #[test]
    fn region_offset_shifts_within_region() {
        let r = region_create(7);
        let r = region_offset(r, constant_i32(100));
        assert_eq!(r.region_id, 7);
        assert_eq!(r.offset, Interval { lo: 100, hi: 100 });
    }

    #[test]
    fn distinct_regions_do_not_alias_under_leq() {
        let a = Region {
            region_id: 1,
            offset: Interval { lo: 0, hi: 4 },
        };
        let b = Region {
            region_id: 2,
            offset: Interval { lo: 0, hi: 4 },
        };
        // a non-bottom region is not ⊑ a different-id region.
        assert!(!region_leq(a, b));
    }
}
