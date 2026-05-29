//! wasm-lattice — interval-domain abstract-domain library as a Wasm
//! component. Exports `pulseengine:wasm-lattice/domain` per
//! `wit/wasm-lattice.wit` (derived from `spar/scry.aadl`, per DD-010).
//!
//! v0.1 ships the interval domain only. Soundness is stated paper-only
//! at v0.1 (per REQ-002 / DD-003); mechanized Rocq proof against
//! WasmCert-Coq lands at v0.9 (FEAT-010).

#![no_std]

use wasm_lattice_component_bindings::exports::pulseengine::wasm_lattice::domain::{
    Guest, Interval, Label, Octagon, Region,
};

extern crate alloc;
use alloc::vec::Vec;

struct Component;

// ── Security-label (taint) domain conversions (FEAT-009, v0.8) ──────
//
// The label lattice algebra lives in the pure `scry_taint` crate so the
// code shipped in this wasm32-wasip2 component is *exactly* the code
// scry-host-tests falsifies natively (the lattice-law tests). The only
// logic local to this file is the trivial enum conversion between the
// WIT-generated `Label` and `scry_taint::Label`.

fn to_taint(l: Label) -> scry_taint::Label {
    match l {
        Label::Low => scry_taint::Label::Low,
        Label::High => scry_taint::Label::High,
    }
}

fn from_taint(l: scry_taint::Label) -> Label {
    match l {
        scry_taint::Label::Low => Label::Low,
        scry_taint::Label::High => Label::High,
    }
}

// ── Octagon relational domain conversions (FEAT-010, v0.9) ──────────
//
// The DBM algebra lives in the pure `scry_octagon` crate so the code
// shipped in this wasm32-wasip2 component is exactly the code
// scry-host-tests falsifies natively. The only logic local to this
// file is the trivial conversion between the WIT-generated `Octagon`
// record (`dim` + flat `Vec<s64>`) and `scry_octagon::Octagon` (same
// shape) — they are field-identical, so it is a move of `m`.

fn to_oct(o: Octagon) -> scry_octagon::Octagon {
    scry_octagon::Octagon { dim: o.dim, m: o.m }
}

fn from_oct(o: scry_octagon::Octagon) -> Octagon {
    Octagon { dim: o.dim, m: o.m }
}

/// Bottom (empty) interval — the conventional encoding is { lo: 1, hi: 0 }.
/// Any interval with `lo > hi` is considered bottom; the constructor
/// canonicalises to { 1, 0 } so equality comparisons work.
const BOTTOM: Interval = Interval { lo: 1, hi: 0 };

/// Top interval — the full i64 range.
const TOP: Interval = Interval {
    lo: i64::MIN,
    hi: i64::MAX,
};

fn is_bot(x: Interval) -> bool {
    x.lo > x.hi
}

fn canon(lo: i64, hi: i64) -> Interval {
    if lo > hi { BOTTOM } else { Interval { lo, hi } }
}

impl Guest for Component {
    fn bottom() -> Interval {
        BOTTOM
    }

    fn top() -> Interval {
        TOP
    }

    fn is_bottom(x: Interval) -> bool {
        is_bot(x)
    }

    fn leq(a: Interval, b: Interval) -> bool {
        if is_bot(a) {
            return true;
        }
        if is_bot(b) {
            return false;
        }
        b.lo <= a.lo && a.hi <= b.hi
    }

    fn join(a: Interval, b: Interval) -> Interval {
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

    fn meet(a: Interval, b: Interval) -> Interval {
        if is_bot(a) || is_bot(b) {
            return BOTTOM;
        }
        canon(a.lo.max(b.lo), a.hi.min(b.hi))
    }

    fn widen(a: Interval, b: Interval) -> Interval {
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

    fn constant_i32(c: i32) -> Interval {
        Interval {
            lo: c as i64,
            hi: c as i64,
        }
    }

    fn constant_i64(c: i64) -> Interval {
        Interval { lo: c, hi: c }
    }

    fn i32_add(a: Interval, b: Interval) -> Interval {
        if is_bot(a) || is_bot(b) {
            return BOTTOM;
        }
        // v0.1: widen to top if the result range straddles i32 wrap.
        // A precise wrap-aware transfer function lands in v0.2.
        let lo = a.lo.saturating_add(b.lo);
        let hi = a.hi.saturating_add(b.hi);
        if lo < i32::MIN as i64 || hi > i32::MAX as i64 {
            TOP
        } else {
            Interval { lo, hi }
        }
    }

    fn i32_sub(a: Interval, b: Interval) -> Interval {
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

    fn i32_mul(a: Interval, b: Interval) -> Interval {
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

    // ── Region domain (FEAT-005, v0.3) ─────────────────────────────
    //
    // A region is `(region-id, offset-interval)`. The lattice on
    // regions is parameterised by region-id equality:
    //
    //   * Same region-id: pointwise on the offset interval
    //     (leq / join / meet / widen all delegate to the
    //     interval ops).
    //   * Different region-id: incomparable — we conservatively
    //     return values that make the analyzer's mismatch-detection
    //     easy without ever silently aliasing two distinct regions.
    //
    // The interval ops we delegate to are the *plain* interval
    // ops, not the i32 saturating ones — region offsets live in
    // an unbounded i64 space (memory.size is a 32-bit byte count
    // but we track signed offsets to keep arithmetic in i64; the
    // analyzer is responsible for catching offsets that escape
    // memory.size via the per-region metadata map).

    fn region_create(region_id: u32) -> Region {
        Region {
            region_id,
            offset: Interval { lo: 0, hi: 0 },
        }
    }

    fn region_offset(r: Region, delta: Interval) -> Region {
        if is_bot(r.offset) || is_bot(delta) {
            return Region {
                region_id: r.region_id,
                offset: BOTTOM,
            };
        }
        // Plain (non-saturating) interval add — region offsets are
        // tracked as signed i64 byte counts; the per-region
        // metadata in the analyzer is what bounds them.
        let lo = r.offset.lo.saturating_add(delta.lo);
        let hi = r.offset.hi.saturating_add(delta.hi);
        Region {
            region_id: r.region_id,
            offset: canon(lo, hi),
        }
    }

    fn region_leq(a: Region, b: Region) -> bool {
        if a.region_id != b.region_id {
            // Different regions: incomparable. Bottom-offset on `a`
            // is conventionally `leq` everything, including a
            // different region, so we special-case it.
            return is_bot(a.offset);
        }
        // Same region: delegate to interval `leq`.
        if is_bot(a.offset) {
            return true;
        }
        if is_bot(b.offset) {
            return false;
        }
        b.offset.lo <= a.offset.lo && a.offset.hi <= b.offset.hi
    }

    fn region_join(a: Region, b: Region) -> Region {
        if a.region_id != b.region_id {
            // Cross-region join: not representable as a single
            // region in v0.3. Return the first operand with offset
            // widened to TOP — the analyzer should generally
            // detect the region-id mismatch before getting here
            // and degrade to a non-region abstract value, but the
            // operator stays total.
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

    fn region_meet(a: Region, b: Region) -> Region {
        if a.region_id != b.region_id {
            // Cross-region meet: empty. Signal via bottom offset on
            // the first operand's region-id so callers can detect.
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

    fn region_widen(a: Region, b: Region) -> Region {
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

    // ── Security-label (taint) domain (FEAT-009, v0.8) ─────────────
    //
    // Delegated to the pure `scry_taint` crate (see the conversion
    // helpers above). The two-point lattice `low ⊑ high`: bottom =
    // low, top = high, join = OR, meet = AND, leq = the chain order.

    fn label_bottom() -> Label {
        from_taint(scry_taint::bottom())
    }

    fn label_top() -> Label {
        from_taint(scry_taint::top())
    }

    fn label_leq(a: Label, b: Label) -> bool {
        scry_taint::leq(to_taint(a), to_taint(b))
    }

    fn label_join(a: Label, b: Label) -> Label {
        from_taint(scry_taint::join(to_taint(a), to_taint(b)))
    }

    fn label_meet(a: Label, b: Label) -> Label {
        from_taint(scry_taint::meet(to_taint(a), to_taint(b)))
    }

    // ── Octagon relational domain (FEAT-010, v0.9) ─────────────────
    //
    // Delegated to the pure `scry_octagon` crate (see the conversion
    // helpers above). The DBM-encoded `±x±y ≤ c` lattice; the shipped
    // relational code is exactly the natively-falsified crate code.

    fn octagon_top(dim: u32) -> Octagon {
        from_oct(scry_octagon::top(dim))
    }

    fn octagon_bottom(dim: u32) -> Octagon {
        from_oct(scry_octagon::bottom(dim))
    }

    fn octagon_is_bottom(o: Octagon) -> bool {
        scry_octagon::is_bottom(&to_oct(o))
    }

    fn octagon_close(o: Octagon) -> Octagon {
        from_oct(scry_octagon::close(&to_oct(o)))
    }

    fn octagon_leq(a: Octagon, b: Octagon) -> bool {
        scry_octagon::leq(&to_oct(a), &to_oct(b))
    }

    fn octagon_join(a: Octagon, b: Octagon) -> Octagon {
        from_oct(scry_octagon::join(&to_oct(a), &to_oct(b)))
    }

    fn octagon_meet(a: Octagon, b: Octagon) -> Octagon {
        from_oct(scry_octagon::meet(&to_oct(a), &to_oct(b)))
    }

    fn octagon_widen(a: Octagon, b: Octagon) -> Octagon {
        from_oct(scry_octagon::widen(&to_oct(a), &to_oct(b)))
    }

    fn octagon_add_bound(o: Octagon, i: u32, j: u32, c: i64) -> Octagon {
        from_oct(scry_octagon::add_bound(&to_oct(o), i, j, c))
    }
}

wasm_lattice_component_bindings::export!(Component with_types_in wasm_lattice_component_bindings);
