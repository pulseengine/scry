//! wasm-lattice — interval-domain abstract-domain library as a Wasm
//! component. Exports `pulseengine:wasm-lattice/domain` per
//! `wit/wasm-lattice.wit` (derived from `spar/scry.aadl`, per DD-010).
//!
//! v0.1 ships the interval domain only. Soundness is stated paper-only
//! at v0.1 (per REQ-002 / DD-003); mechanized Rocq proof against
//! WasmCert-Coq lands at v0.9 (FEAT-010).

#![no_std]

use wasm_lattice_component_bindings::exports::pulseengine::wasm_lattice::domain::{
    Guest, Interval,
};

struct Component;

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
    if lo > hi {
        BOTTOM
    } else {
        Interval { lo, hi }
    }
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
}

wasm_lattice_component_bindings::export!(Component with_types_in wasm_lattice_component_bindings);
