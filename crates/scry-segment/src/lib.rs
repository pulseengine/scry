#![no_std]
#![forbid(unsafe_code)]
//! # scry-sai-segment — linear-memory segmentation over interval content
//!
//! FEAT-058 (AC-015; Cousot, Cousot & Logozzo, *A parametric segmentation
//! functor for fully automatic and scalable array content analysis*, POPL
//! 2011; DD-018). This is the pure, Wasm-agnostic core of scry's
//! content-sensitive memory: an **abstract array** mapping integer offsets to
//! [`scry_interval`] content, instead of the one havoc'd `⊤` blob the region
//! domain uses today (REQ-019).
//!
//! ## Representation
//!
//! A [`Segmentation`] is a sorted, disjoint list of half-open segments
//! `[lo, hi)`, each carrying an interval `val` that every offset it covers is
//! constrained to. Offsets covered by **no** segment are unconstrained (`⊤`):
//! the canonical form therefore stores *only* non-trivial constraints and
//! never stores a `⊤` segment.
//!
//! ## Concretization
//!
//! A concrete memory is a map `m : offset → value`. Then
//!
//! ```text
//!   γ(S) = { m | ∀ seg ∈ S. ∀ o ∈ [seg.lo, seg.hi). seg.val.lo ≤ m(o) ≤ seg.val.hi }
//! ```
//!
//! `⊤` (empty segment list) admits every memory. A segment whose `val` is
//! `⊥` (empty interval) covering ≥1 offset makes `γ(S) = ∅` (an unreachable
//! memory) — allowed, and sound.
//!
//! ## Soundness discipline (DD-018)
//!
//! Every operation over-approximates. The keystone is **weak-by-default**:
//! [`Segmentation::weak_store`] over a range of possible addresses joins the
//! stored value into the old content of *every* possibly-touched offset (it
//! never overwrites), so a store whose address scry cannot pin to a single
//! offset can only *lose* precision, never claim a value the concrete run
//! might not have. A **strong** overwrite ([`Segmentation::strong_store`]) is
//! used only for a singleton offset. All Wasm-specific concerns — store
//! widths, byte-level aliasing of overlapping multi-byte accesses — are
//! handled soundly by the analyzer wiring (FEAT-058 slice 2) on top of this
//! offset-granular core, not here.
//!
//! The lattice/order/join/store/load soundness is γ-swept natively (below) and
//! mechanized admit-free in `proofs/rocq/Segment.v`.

extern crate alloc;
use alloc::vec::Vec;

pub use scry_interval::Interval;
use scry_interval::{self as iv};

/// One half-open segment `[lo, hi)` constraining every covered offset to `val`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Seg {
    /// Inclusive low offset.
    pub lo: i64,
    /// Exclusive high offset (`lo < hi`).
    pub hi: i64,
    /// Interval every offset in `[lo, hi)` is constrained to.
    pub val: Interval,
}

/// A content-sensitive abstraction of one linear-memory region: a sorted,
/// disjoint, `⊤`-free list of [`Seg`]s. See the module docs for `γ`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Segmentation {
    segs: Vec<Seg>,
}

/// The fully-unconstrained memory (`⊤`): admits every concrete memory.
pub fn top() -> Segmentation {
    Segmentation { segs: Vec::new() }
}

impl Segmentation {
    /// Read-only view of the canonical segment list.
    pub fn segments(&self) -> &[Seg] {
        &self.segs
    }

    /// Is this the top (unconstrained) memory?
    pub fn is_top(&self) -> bool {
        self.segs.is_empty()
    }

    /// The constraint this abstraction places on a single offset — the
    /// covering segment's `val`, or `⊤` if the offset is unconstrained.
    pub fn constraint_at(&self, off: i64) -> Interval {
        for s in &self.segs {
            if s.lo <= off && off < s.hi {
                return s.val;
            }
        }
        iv::TOP
    }

    /// Build a canonical `Segmentation` from a list of (possibly noncanonical,
    /// but disjoint and offset-sorted) `[lo, hi)` → val ranges: drop empty and
    /// `⊤` ranges, and coalesce adjacent ranges carrying an equal `val`.
    fn from_sorted_ranges(mut ranges: Vec<Seg>) -> Segmentation {
        let mut segs: Vec<Seg> = Vec::new();
        for r in ranges.drain(..) {
            if r.hi <= r.lo || r.val == iv::TOP {
                continue;
            }
            match segs.last_mut() {
                Some(prev) if prev.hi == r.lo && prev.val == r.val => prev.hi = r.hi,
                _ => segs.push(r),
            }
        }
        Segmentation { segs }
    }

    /// The sorted, de-duplicated boundary offsets of two abstractions — every
    /// point at which either one's constraint can change. Between consecutive
    /// boundaries each abstraction's constraint is constant, so a single
    /// [`constraint_at`](Self::constraint_at) probe per sub-range is exact.
    fn boundaries(a: &Segmentation, b: &Segmentation) -> Vec<i64> {
        let mut pts: Vec<i64> = Vec::new();
        for s in a.segs.iter().chain(b.segs.iter()) {
            pts.push(s.lo);
            pts.push(s.hi);
        }
        pts.sort_unstable();
        pts.dedup();
        pts
    }

    /// Order: `self ⊑ other` iff `γ(self) ⊆ γ(other)` — i.e. at every offset
    /// `self`'s constraint is at least as tight as `other`'s.
    pub fn leq(&self, other: &Segmentation) -> bool {
        let pts = Self::boundaries(self, other);
        pts.windows(2).all(|w| {
            let probe = w[0];
            iv::leq(self.constraint_at(probe), other.constraint_at(probe))
        }) && {
            // Sub-ranges strictly outside every boundary are `⊤` in both, and
            // `⊤ ⊑ ⊤` holds trivially — no extra check needed.
            true
        }
    }

    /// Join (least upper bound over `γ`): a memory admitted by either operand
    /// is admitted by the result. An offset is constrained in the join only
    /// where **both** operands constrain it, to the interval-join of the two.
    pub fn join(&self, other: &Segmentation) -> Segmentation {
        self.combine(other, iv::join)
    }

    /// Widening: like [`join`](Self::join) but interval-*widens* each matched
    /// segment and caps the segment count, so ascending chains stabilise.
    pub fn widen(&self, other: &Segmentation) -> Segmentation {
        let w = self.combine(other, iv::widen);
        if w.segs.len() > MAX_SEGMENTS {
            // Bounded height: beyond the cap, forget structure (sound — `⊤`
            // over-approximates any memory). Guarantees loop termination.
            top()
        } else {
            w
        }
    }

    /// Shared boundary-walk for [`join`](Self::join) / [`widen`](Self::widen):
    /// combine the two abstractions' per-offset constraints with `f`.
    fn combine(&self, other: &Segmentation, f: fn(Interval, Interval) -> Interval) -> Segmentation {
        let pts = Self::boundaries(self, other);
        let mut ranges: Vec<Seg> = Vec::new();
        for w in pts.windows(2) {
            let (lo, hi) = (w[0], w[1]);
            let v = f(self.constraint_at(lo), other.constraint_at(lo));
            ranges.push(Seg { lo, hi, val: v });
        }
        Self::from_sorted_ranges(ranges)
    }

    /// **Strong** update: record that the single offset `off` now holds a value
    /// in `val`, overwriting any prior constraint there. Sound as the abstract
    /// transfer of `m' = m[off ↦ v], v ∈ γ(val)` **only** because `off` is a
    /// singleton offset (see [`weak_store`](Self::weak_store) otherwise).
    pub fn strong_store(&self, off: i64, val: Interval) -> Segmentation {
        self.rewrite_range(off, off + 1, |_old| val)
    }

    /// **Weak** update over a range of possible addresses `[lo, hi)`: the value
    /// at each covered offset becomes the interval-join of its old content and
    /// `val` (it might be untouched, or might be the stored value — scry does
    /// not know which offset was written). Never overwrites: this is the
    /// soundness keystone for imprecise store addresses (DD-018).
    pub fn weak_store(&self, lo: i64, hi: i64, val: Interval) -> Segmentation {
        self.rewrite_range(lo, hi, |old| iv::join(old, val))
    }

    /// Rewrite the content of every offset in `[lo, hi)` by `f(old)`, leaving
    /// offsets outside the range untouched. The boundary walk includes `lo`
    /// and `hi`, so every produced sub-range is wholly inside or wholly outside
    /// the rewritten range.
    fn rewrite_range(&self, lo: i64, hi: i64, f: impl Fn(Interval) -> Interval) -> Segmentation {
        if hi <= lo {
            return self.clone();
        }
        let mut pts: Vec<i64> = Vec::with_capacity(self.segs.len() * 2 + 2);
        for s in &self.segs {
            pts.push(s.lo);
            pts.push(s.hi);
        }
        pts.push(lo);
        pts.push(hi);
        pts.sort_unstable();
        pts.dedup();

        let mut ranges: Vec<Seg> = Vec::new();
        for w in pts.windows(2) {
            let (x, y) = (w[0], w[1]);
            let old = self.constraint_at(x);
            let v = if x >= lo && x < hi { f(old) } else { old };
            ranges.push(Seg { lo: x, hi: y, val: v });
        }
        Self::from_sorted_ranges(ranges)
    }

    /// Load from a single known offset: the tightest interval containing
    /// `m(off)` for every `m ∈ γ(self)` — the covering constraint, or `⊤`.
    pub fn load(&self, off: i64) -> Interval {
        self.constraint_at(off)
    }

    /// Load from an unknown address in `[lo, hi)`: the interval-join of the
    /// content of every possibly-addressed offset (`⊤` if any is
    /// unconstrained; `⊥` if the range is empty). Sound: the loaded value is
    /// `m(a)` for some `a ∈ [lo, hi)`, which lies in some joined constraint.
    pub fn load_range(&self, lo: i64, hi: i64) -> Interval {
        if hi <= lo {
            return iv::BOTTOM;
        }
        let mut pts: Vec<i64> = Vec::new();
        for s in &self.segs {
            if s.lo < hi && s.hi > lo {
                pts.push(s.lo.max(lo));
                pts.push(s.hi.min(hi));
            }
        }
        pts.push(lo);
        pts.push(hi);
        pts.sort_unstable();
        pts.dedup();

        let mut acc = iv::BOTTOM;
        for w in pts.windows(2) {
            acc = iv::join(acc, self.constraint_at(w[0]));
        }
        acc
    }
}

/// Segment-count cap for [`Segmentation::widen`] — the abstract domain's height
/// bound that guarantees fixpoint termination.
pub const MAX_SEGMENTS: usize = 64;

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn ival(lo: i64, hi: i64) -> Interval {
        iv::canon(lo, hi)
    }

    /// Build a `Segmentation` from raw ranges (test helper — canonicalises).
    fn seg(ranges: &[(i64, i64, Interval)]) -> Segmentation {
        let mut v: Vec<Seg> = ranges
            .iter()
            .map(|&(lo, hi, val)| Seg { lo, hi, val })
            .collect();
        v.sort_by_key(|s| s.lo);
        Segmentation::from_sorted_ranges(v)
    }

    // ── γ-sweep scaffolding ────────────────────────────────────────────────
    const DOM: i64 = 4; // offsets 0..4
    const VLO: i64 = -1;
    const VHI: i64 = 2; // values -1..=2

    /// γ membership: does concrete memory `m` (offsets 0..DOM) satisfy `s`?
    fn gamma(s: &Segmentation, m: &[i64; DOM as usize]) -> bool {
        (0..DOM).all(|o| {
            let c = s.constraint_at(o);
            c.lo <= m[o as usize] && m[o as usize] <= c.hi
        })
    }

    /// Enumerate every concrete memory over offsets 0..DOM, values VLO..=VHI.
    fn all_mems() -> Vec<[i64; DOM as usize]> {
        let mut out = Vec::new();
        let mut m = [VLO; DOM as usize];
        loop {
            out.push(m);
            // odometer increment
            let mut i = 0;
            loop {
                if i == DOM as usize {
                    return out;
                }
                m[i] += 1;
                if m[i] <= VHI {
                    break;
                }
                m[i] = VLO;
                i += 1;
            }
        }
    }

    /// A small, structurally varied family of abstractions for the sweep.
    fn samples() -> Vec<Segmentation> {
        vec![
            top(),
            seg(&[(0, 2, ival(0, 1))]),
            seg(&[(1, 3, ival(-1, 0))]),
            seg(&[(0, 4, ival(0, 0))]),
            seg(&[(2, 3, ival(1, 2))]),
            seg(&[(0, 1, ival(-1, 1)), (2, 4, ival(0, 2))]),
            seg(&[(0, 2, ival(0, 2)), (2, 4, ival(-1, 1))]),
            seg(&[(1, 2, ival(2, 2))]),
        ]
    }

    fn small_ivals() -> Vec<Interval> {
        vec![
            ival(0, 0),
            ival(-1, 1),
            ival(1, 2),
            ival(0, 2),
            iv::TOP,
        ]
    }

    #[test]
    fn leq_is_gamma_sound_and_reflexive() {
        let ss = samples();
        let ms = all_mems();
        for a in &ss {
            assert!(a.leq(a), "leq reflexive");
            for b in &ss {
                if a.leq(b) {
                    for m in &ms {
                        assert!(
                            !gamma(a, m) || gamma(b, m),
                            "leq(a,b) but γ(a) ⊄ γ(b) at {m:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn join_over_approximates_union_and_is_upper_bound() {
        let ss = samples();
        let ms = all_mems();
        for a in &ss {
            for b in &ss {
                let j = a.join(b);
                // upper bound in the order
                assert!(a.leq(&j), "a ⊑ a⊔b");
                assert!(b.leq(&j), "b ⊑ a⊔b");
                // γ-soundness
                for m in &ms {
                    if gamma(a, m) || gamma(b, m) {
                        assert!(gamma(&j, m), "γ(a)∪γ(b) ⊄ γ(a⊔b) at {m:?}");
                    }
                }
            }
        }
    }

    #[test]
    fn widen_is_an_upper_bound() {
        let ss = samples();
        for a in &ss {
            for b in &ss {
                let w = a.widen(b);
                assert!(b.leq(&w), "b ⊑ a▽b");
            }
        }
    }

    #[test]
    fn strong_store_is_gamma_sound() {
        let ss = samples();
        let ms = all_mems();
        for a in &ss {
            for off in 0..DOM {
                for &val in &small_ivals() {
                    let s = a.strong_store(off, val);
                    for m in &ms {
                        if !gamma(a, m) {
                            continue;
                        }
                        for v in VLO..=VHI {
                            if !(val.lo <= v && v <= val.hi) {
                                continue;
                            }
                            let mut m2 = *m;
                            m2[off as usize] = v;
                            assert!(
                                gamma(&s, &m2),
                                "strong_store unsound: off={off} v={v} m={m:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn weak_store_is_gamma_sound() {
        let ss = samples();
        let ms = all_mems();
        for a in &ss {
            // weak store over ranges [lo,hi) within the domain
            for lo in 0..DOM {
                for hi in (lo + 1)..=DOM {
                    for &val in &small_ivals() {
                        let s = a.weak_store(lo, hi, val);
                        for m in &ms {
                            if !gamma(a, m) {
                                continue;
                            }
                            // the write hit *some* address in [lo,hi) with some v∈val
                            for addr in lo..hi {
                                for v in VLO..=VHI {
                                    if !(val.lo <= v && v <= val.hi) {
                                        continue;
                                    }
                                    let mut m2 = *m;
                                    m2[addr as usize] = v;
                                    assert!(
                                        gamma(&s, &m2),
                                        "weak_store unsound: [{lo},{hi}) addr={addr} v={v}"
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn load_contains_every_concrete_value() {
        let ss = samples();
        let ms = all_mems();
        for a in &ss {
            for off in 0..DOM {
                let l = a.load(off);
                for m in &ms {
                    if gamma(a, m) {
                        let v = m[off as usize];
                        assert!(l.lo <= v && v <= l.hi, "load({off}) ⊉ {v}");
                    }
                }
            }
        }
    }

    #[test]
    fn load_range_contains_every_addressable_value() {
        let ss = samples();
        let ms = all_mems();
        for a in &ss {
            for lo in 0..DOM {
                for hi in (lo + 1)..=DOM {
                    let l = a.load_range(lo, hi);
                    for m in &ms {
                        if !gamma(a, m) {
                            continue;
                        }
                        for addr in lo..hi {
                            let v = m[addr as usize];
                            assert!(l.lo <= v && v <= l.hi, "load_range[{lo},{hi}) ⊉ {v}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn strong_then_load_round_trips() {
        // The headline capability: store a bounded value, load it back exactly.
        let s = top().strong_store(8, ival(3, 5));
        assert_eq!(s.load(8), ival(3, 5));
        assert_eq!(s.load(9), iv::TOP); // untouched offset stays ⊤
    }

    #[test]
    fn top_admits_everything() {
        let t = top();
        assert!(t.is_top());
        for m in &all_mems() {
            assert!(gamma(&t, m));
        }
    }

    #[test]
    fn canonical_form_has_no_top_or_adjacent_equal_segments() {
        let s = seg(&[(0, 2, ival(0, 1)), (2, 4, ival(0, 1)), (4, 6, iv::TOP)]);
        // adjacent equal [0,2)+[2,4) coalesce; the ⊤ range drops
        assert_eq!(s.segments().len(), 1);
        assert_eq!(s.segments()[0], Seg { lo: 0, hi: 4, val: ival(0, 1) });
    }
}
