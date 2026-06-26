//! scry-bits — the pure known-bits × interval-guarded congruence reduced
//! product for scry (FEAT-037, DD-017).
//!
//! This crate holds the *algebra* of a bit/alignment/stride abstract domain
//! and nothing else: no Wasm parsing, no WIT bindings, no I/O. It is the
//! sibling of [`scry-interval`] / [`scry-octagon`] — a pure, dependency-free
//! crate that compiles `#![no_std]` AND natively (where its own γ-sweep tests
//! falsify the lattice laws + concretization soundness, *including* the
//! wrapping machine-integer semantics).
//!
//! ## The two components
//!
//! Both are taken over a fixed bit width `w` (32 or 64 for Wasm; the tests use
//! `w = 8` to enumerate the whole concrete domain exhaustively). A value is
//! interpreted as the `w`-bit unsigned integer `x ∈ [0, 2^w)`.
//!
//! * **Known-bits** ([`KnownBits`]) — LLVM's `KnownBits`. Each bit is
//!   *known-0*, *known-1*, or *unknown* (⊤). Stored as `(zeros, ones)` with the
//!   well-formedness invariant `zeros & ones == 0`; a conflict is ⊥.
//!   `γ(zeros, ones) = { x | x & zeros == 0 ∧ x & ones == ones }`.
//!
//! * **Congruence** ([`Cong`]) — Granger's domain: `x ≡ r (mod m)`, stored as
//!   `Mod { m, r }` with `m ≥ 1` (`m == 1` is ⊤) and `0 ≤ r < m`; ⊥ is empty.
//!   `γ(Mod{m,r}) = { x | x ≡ r (mod m) }`.
//!
//! ## The soundness subtlety (why DD-017 exists)
//!
//! Wasm integer arithmetic *wraps* mod `2^w`. A congruence is preserved by a
//! wrapping `add`/`sub`/`mul` **only when `m` divides `2^w`** — i.e. `m` is a
//! power of two. The load-bearing fact (mechanized admit-free in
//! `proofs/rocq/BitsCongruence.v`) is:
//!
//! ```text
//!   (x + y) mod 2^w  ≡  r1 + r2   (mod gcd(m, 2^w))
//! ```
//!
//! and `≡ (mod m)` *exactly* when no wrap occurred. So the transfers take a
//! `wrap_free` flag (supplied by the analyzer from the interval domain): when
//! the operation provably cannot overflow the full modulus `m` is retained;
//! otherwise it is weakened to `gcd(m, 2^w) = 2^min(v2(m), w)` — always a power
//! of two, so always sound under wrap. This is what lets a non-power-of-two
//! stride (`i ≡ 2 (mod 3)`) survive soundly across a guarded increment.
//!
//! Note `gcd(m, 2^w)` is computed as `2^min(v2(m), w)` (a trailing-zeros count),
//! which never needs the unrepresentable `2^64`.
//!
//! ## The reduced product
//!
//! [`BitsCong`] pairs the two with a [`BitsCong::reduce`] operator that
//! co-propagates facts: a fixed low-bit prefix in known-bits gives a `2^k`
//! congruence and vice-versa (the 2-adic residue). `reduce` only ever *removes
//! non-concretizable points* — `γ(reduce a) == γ(a)` — so it is sound by
//! construction.
//!
//! ## Soundness role (REQ-001, G-005)
//!
//! Every public transfer `f#` is a sound over-approximation: for all concrete
//! inputs in the operands' concretizations, the concrete (wrapping) result is
//! in `γ(f#(...))`. The crate's tests assert exactly this by an exhaustive
//! γ-sweep at `w = 8`. The companion value is always a *sound companion* to the
//! interval: where a transfer is unmodelled the result is ⊤, which is sound.

#![cfg_attr(not(test), no_std)]

// ─────────────────────────── width helpers ───────────────────────────

/// The all-ones mask for a `w`-bit value (`w ∈ 1..=64`). `w == 64` ⇒ all 64.
#[inline]
pub fn width_mask(w: u32) -> u64 {
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// `2^w` is unrepresentable for `w == 64`; we only ever need `gcd(m, 2^w)`,
/// which is `2^min(v2(m), w)`. This returns that power of two for `m ≥ 1`.
/// (`v2(m)` = number of trailing zero bits of `m`.)
#[inline]
fn gcd_with_pow2(m: u64, w: u32) -> u64 {
    debug_assert!(m >= 1);
    let v2 = m.trailing_zeros().min(w);
    // v2 ≤ w ≤ 64, and for m ≥ 1 a u64 has at most 63 trailing zeros, so the
    // shift is in range whenever it could matter (w == 64 ⇒ v2 ≤ 63).
    1u64 << v2
}

/// Binary gcd of two `u64`s. `gcd(0, x) == x`.
#[inline]
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// `lcm` with saturation: returns `None` if the true lcm would exceed `u64`
/// (the caller then keeps the coarser modulus — sound, since a larger modulus
/// is a *weaker* constraint and we only ever use lcm to *tighten* in `meet`).
#[inline]
fn checked_lcm(a: u64, b: u64) -> Option<u64> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd(a, b);
    (a / g).checked_mul(b)
}

// ─────────────────────────── known-bits ───────────────────────────

/// Per-bit known-value lattice (LLVM `KnownBits`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KnownBits {
    /// The empty set — an impossible value (some bit is both 0 and 1).
    Bottom,
    /// `x & zeros == 0` (those bits are known 0) and `x & ones == ones` (those
    /// bits are known 1). Invariant: `zeros & ones == 0` (masked to width).
    Bits { zeros: u64, ones: u64 },
}

impl KnownBits {
    /// ⊤ — nothing known.
    #[inline]
    pub fn top() -> Self {
        KnownBits::Bits { zeros: 0, ones: 0 }
    }

    /// ⊥ — the empty set.
    #[inline]
    pub fn bottom() -> Self {
        KnownBits::Bottom
    }

    /// Construct from raw masks at width `w`, normalizing: bits outside `w` are
    /// dropped, and a `zeros & ones` conflict collapses to ⊥.
    #[inline]
    pub fn new(zeros: u64, ones: u64, w: u32) -> Self {
        let mask = width_mask(w);
        let z = zeros & mask;
        let o = ones & mask;
        if z & o != 0 {
            KnownBits::Bottom
        } else {
            KnownBits::Bits { zeros: z, ones: o }
        }
    }

    /// The exact known-bits of a concrete constant `c` at width `w`.
    #[inline]
    pub fn constant(c: u64, w: u32) -> Self {
        let mask = width_mask(w);
        KnownBits::new(!c & mask, c & mask, w)
    }

    /// Does `x` (a `w`-bit value) satisfy these known bits?
    #[inline]
    pub fn contains(&self, x: u64, w: u32) -> bool {
        let mask = width_mask(w);
        match *self {
            KnownBits::Bottom => false,
            KnownBits::Bits { zeros, ones } => {
                let x = x & mask;
                (x & zeros) == 0 && (x & ones) == ones
            }
        }
    }

    /// `self ⊑ other` (γ(self) ⊆ γ(other)): every bit `other` fixes, `self`
    /// fixes the same way.
    #[inline]
    pub fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (KnownBits::Bottom, _) => true,
            (_, KnownBits::Bottom) => false,
            (
                KnownBits::Bits {
                    zeros: z1,
                    ones: o1,
                },
                KnownBits::Bits {
                    zeros: z2,
                    ones: o2,
                },
            ) => (z2 & !z1) == 0 && (o2 & !o1) == 0,
        }
    }

    /// Join (⊔) — a bit is known in the result only if known *and equal* in
    /// both. Over-approximates the union.
    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        match (*self, *other) {
            (KnownBits::Bottom, x) | (x, KnownBits::Bottom) => x,
            (
                KnownBits::Bits {
                    zeros: z1,
                    ones: o1,
                },
                KnownBits::Bits {
                    zeros: z2,
                    ones: o2,
                },
            ) => KnownBits::Bits {
                zeros: z1 & z2,
                ones: o1 & o2,
            },
        }
    }

    /// Meet (⊓) — union the known bits; a disagreement is ⊥.
    #[inline]
    pub fn meet(&self, other: &Self, w: u32) -> Self {
        match (*self, *other) {
            (KnownBits::Bottom, _) | (_, KnownBits::Bottom) => KnownBits::Bottom,
            (
                KnownBits::Bits {
                    zeros: z1,
                    ones: o1,
                },
                KnownBits::Bits {
                    zeros: z2,
                    ones: o2,
                },
            ) => KnownBits::new(z1 | z2, o1 | o2, w),
        }
    }

    /// Number of contiguous *known* low bits (from bit 0 up to the first
    /// unknown), capped at `w`. Used by the reduction to read a 2-adic residue.
    #[inline]
    fn trailing_known(&self, w: u32) -> u32 {
        match *self {
            KnownBits::Bottom => w,
            KnownBits::Bits { zeros, ones } => {
                let known = (zeros | ones) & width_mask(w);
                // first unknown bit = first 0 in `known`.
                (!known).trailing_zeros().min(w)
            }
        }
    }

    /// The value of the low `k` bits (assumes they are known; 0 for unknown).
    #[inline]
    fn low_bits_value(&self, k: u32) -> u64 {
        match *self {
            KnownBits::Bottom => 0,
            KnownBits::Bits { ones, .. } => {
                if k == 0 {
                    0
                } else {
                    ones & ((1u64 << k) - 1)
                }
            }
        }
    }
}

// ─────────────────────────── congruence ───────────────────────────

/// Congruence lattice: `x ≡ r (mod m)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cong {
    /// The empty set.
    Bottom,
    /// `x ≡ r (mod m)`. Conventions (standard Granger domain):
    ///   * `m == 0` ⇒ the **singleton** `{ r }` (the convention
    ///     `a ≡ b (mod 0) ⟺ a = b`, `gcd(0, n) = n`);
    ///   * `m == 1` ⇒ ⊤ (every value);
    ///   * `m ≥ 2` ⇒ `x ≡ r (mod m)` with `0 ≤ r < m`.
    Mod { m: u64, r: u64 },
}

impl Cong {
    /// ⊤ — every value (`mod 1`).
    #[inline]
    pub fn top() -> Self {
        Cong::Mod { m: 1, r: 0 }
    }

    /// ⊥.
    #[inline]
    pub fn bottom() -> Self {
        Cong::Bottom
    }

    /// The singleton `{ c }`.
    #[inline]
    pub fn singleton(c: u64) -> Self {
        Cong::Mod { m: 0, r: c }
    }

    /// Construct `x ≡ r (mod m)`, normalizing `r` into `[0, m)`. `m == 0` is the
    /// singleton `{ r }`; `m == 1` is ⊤.
    #[inline]
    pub fn new(m: u64, r: u64) -> Self {
        match m {
            0 => Cong::Mod { m: 0, r },
            1 => Cong::top(),
            _ => Cong::Mod { m, r: r % m },
        }
    }

    /// Does `x` satisfy this congruence?
    #[inline]
    pub fn contains(&self, x: u64) -> bool {
        match *self {
            Cong::Bottom => false,
            Cong::Mod { m: 0, r } => x == r,
            Cong::Mod { m, r } => x % m == r,
        }
    }

    /// `self ⊑ other`: every value `self` admits, `other` admits.
    #[inline]
    pub fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Cong::Bottom, _) => true,
            (_, Cong::Bottom) => false,
            // A singleton ⊑ other iff other contains the point.
            (Cong::Mod { m: 0, r }, o) => o.contains(*r),
            // self ≡ r1 (mod m1), m1 ≥ 1: ⊑ singleton only if m1 == 0 (handled),
            // so a non-singleton is never ⊑ a singleton.
            (_, Cong::Mod { m: 0, .. }) => false,
            (Cong::Mod { m: m1, r: r1 }, Cong::Mod { m: m2, r: r2 }) => {
                m1 % m2 == 0 && r1 % m2 == *r2
            }
        }
    }

    /// Join (⊔): the strongest congruence containing both. Granger:
    /// `m = gcd(m1, m2, |r1 - r2|)`, `r = r1 mod m`.
    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Cong::Bottom, x) | (x, Cong::Bottom) => x,
            (Cong::Mod { m: m1, r: r1 }, Cong::Mod { m: m2, r: r2 }) => {
                let diff = r1.abs_diff(r2);
                let g = gcd(gcd(m1, m2), diff);
                Cong::new(g, r1)
            }
        }
    }

    /// Meet (⊓): CRT intersection. Empty (⊥) if the residues are incompatible
    /// mod `gcd(m1, m2)`. If the lcm overflows `u64`, keep the coarser of the
    /// two inputs (sound: it still contains the true intersection).
    #[inline]
    pub fn meet(&self, other: &Self) -> Self {
        match (*self, *other) {
            (Cong::Bottom, _) | (_, Cong::Bottom) => Cong::Bottom,
            // A singleton ⊓ X is the singleton if X contains the point, else ⊥.
            (s @ Cong::Mod { m: 0, r }, o) | (o, s @ Cong::Mod { m: 0, r }) => {
                if o.contains(r) {
                    s
                } else {
                    Cong::Bottom
                }
            }
            (Cong::Mod { m: m1, r: r1 }, Cong::Mod { m: m2, r: r2 }) => {
                let g = gcd(m1, m2);
                if (r1 % g) != (r2 % g) {
                    return Cong::Bottom;
                }
                match checked_lcm(m1, m2) {
                    Some(l) => {
                        // Search the residue in [0, l) congruent to both. l/m1
                        // ≤ m2 steps; cheap for the small moduli we track.
                        let mut x = r1;
                        while x % m2 != r2 {
                            x += m1;
                        }
                        Cong::new(l, x)
                    }
                    None => {
                        // Keep the finer (larger-modulus) input.
                        if m1 >= m2 {
                            Cong::Mod { m: m1, r: r1 }
                        } else {
                            Cong::Mod { m: m2, r: r2 }
                        }
                    }
                }
            }
        }
    }

    /// The modulus (1 for ⊤/⊥-as-no-info). Helper for transfers.
    #[inline]
    fn modulus(&self) -> u64 {
        match *self {
            Cong::Bottom => 1,
            Cong::Mod { m, .. } => m,
        }
    }

    #[inline]
    fn residue(&self) -> u64 {
        match *self {
            Cong::Bottom => 0,
            Cong::Mod { r, .. } => r,
        }
    }
}

/// The common modulus and residues for a binary op: `x ≡ r1`, `y ≡ r2` both
/// taken `mod g = gcd(m1, m2)`. Returns `None` if either operand is ⊥, and
/// `g == 0` exactly when BOTH operands are singletons (then the residues are
/// the exact values, returned unreduced — `% 0` would panic).
#[inline]
fn common_mod(a: &Cong, b: &Cong) -> Option<(u64, u64, u64)> {
    if matches!(a, Cong::Bottom) || matches!(b, Cong::Bottom) {
        return None;
    }
    let g = gcd(a.modulus(), b.modulus());
    if g == 0 {
        Some((0, a.residue(), b.residue()))
    } else {
        Some((g, a.residue() % g, b.residue() % g))
    }
}

/// Congruence transfer for `x + y` at width `w`. `wrap_free` ⇒ the analyzer
/// proved the exact-ℤ sum stays in range, so the full gcd modulus is sound;
/// otherwise weaken to `gcd(g, 2^w)`.
#[inline]
pub fn cong_add(a: &Cong, b: &Cong, w: u32, wrap_free: bool) -> Cong {
    match common_mod(a, b) {
        None => Cong::Bottom,
        // Both singletons ⇒ the wrapped sum is itself a constant (exact, no
        // weakening needed even under wrap).
        Some((0, r1, r2)) => Cong::singleton(r1.wrapping_add(r2) & width_mask(w)),
        Some((g, r1, r2)) => {
            let m = if wrap_free { g } else { gcd_with_pow2(g, w) };
            Cong::new(m, (r1 + r2) % m)
        }
    }
}

/// Congruence transfer for `x - y` at width `w`.
#[inline]
pub fn cong_sub(a: &Cong, b: &Cong, w: u32, wrap_free: bool) -> Cong {
    match common_mod(a, b) {
        None => Cong::Bottom,
        Some((0, r1, r2)) => Cong::singleton(r1.wrapping_sub(r2) & width_mask(w)),
        Some((g, r1, r2)) => {
            let m = if wrap_free { g } else { gcd_with_pow2(g, w) };
            // (r1 - r2) mod m, computed without going negative.
            let r = ((r1 % m) + m - (r2 % m)) % m;
            Cong::new(m, r)
        }
    }
}

/// Congruence transfer for `x * y` at width `w`. `x·y ≡ r1·r2 (mod g)` with
/// `g = gcd(m1, m2)`; weaken to `gcd(g, 2^w)` if the product may wrap.
#[inline]
pub fn cong_mul(a: &Cong, b: &Cong, w: u32, wrap_free: bool) -> Cong {
    match common_mod(a, b) {
        None => Cong::Bottom,
        Some((0, r1, r2)) => Cong::singleton(r1.wrapping_mul(r2) & width_mask(w)),
        Some((g, r1, r2)) => {
            let m = if wrap_free { g } else { gcd_with_pow2(g, w) };
            // r1·r2 mod m without overflowing: reduce factors first.
            let prod = (r1 % m).wrapping_mul(r2 % m) % m;
            Cong::new(m, prod)
        }
    }
}

// ───────────────────── reduced product ─────────────────────

/// The reduced product `KnownBits × Cong`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BitsCong {
    pub kb: KnownBits,
    pub cong: Cong,
}

impl BitsCong {
    /// ⊤ — nothing known.
    #[inline]
    pub fn top() -> Self {
        BitsCong {
            kb: KnownBits::top(),
            cong: Cong::top(),
        }
    }

    /// ⊥.
    #[inline]
    pub fn bottom() -> Self {
        BitsCong {
            kb: KnownBits::Bottom,
            cong: Cong::Bottom,
        }
    }

    /// True if either component is ⊥ (the product is empty).
    #[inline]
    pub fn is_bottom(&self) -> bool {
        matches!(self.kb, KnownBits::Bottom) || matches!(self.cong, Cong::Bottom)
    }

    /// A concrete constant.
    #[inline]
    pub fn constant(c: u64, w: u32) -> Self {
        // Exactness lives in BOTH components: known-bits fixes every bit, and
        // the congruence is the singleton `{c}` (modulus 0). The singleton
        // encoding is what lets `join` of constants recover an odd modulus
        // (e.g. join {2} {5} = ≡2 mod 3 via gcd(0,0,3)).
        let mask = width_mask(w);
        BitsCong {
            kb: KnownBits::constant(c, w),
            cong: Cong::singleton(c & mask),
        }
    }

    /// Does `x` satisfy both components?
    #[inline]
    pub fn contains(&self, x: u64, w: u32) -> bool {
        self.kb.contains(x, w) && self.cong.contains(x & width_mask(w))
    }

    /// `self ⊑ other` (both components).
    #[inline]
    pub fn leq(&self, other: &Self) -> bool {
        // A ⊥ in either component means the empty set ⊑ anything.
        if self.is_bottom() {
            return true;
        }
        if other.is_bottom() {
            return false;
        }
        self.kb.leq(&other.kb) && self.cong.leq(&other.cong)
    }

    /// Join — componentwise, then reduce.
    #[inline]
    pub fn join(&self, other: &Self, w: u32) -> Self {
        if self.is_bottom() {
            return *other;
        }
        if other.is_bottom() {
            return *self;
        }
        BitsCong {
            kb: self.kb.join(&other.kb),
            cong: self.cong.join(&other.cong),
        }
        .reduce(w)
    }

    /// Meet — componentwise, then reduce. ⊥ if any component conflicts.
    #[inline]
    pub fn meet(&self, other: &Self, w: u32) -> Self {
        BitsCong {
            kb: self.kb.meet(&other.kb, w),
            cong: self.cong.meet(&other.cong),
        }
        .reduce(w)
    }

    /// The reduction operator: co-propagate facts between the two components
    /// until a fixpoint (one round suffices for the 2-adic exchange).
    ///
    /// * known-bits → congruence: the low `k` contiguous known bits give
    ///   `x ≡ (low k bits) (mod 2^k)`.
    /// * congruence → known-bits: a modulus with `v2(m) = j` and residue `r`
    ///   fixes the low `j` bits of `x` to `r mod 2^j`.
    ///
    /// `reduce` only makes implicit facts explicit, so `γ(reduce a) == γ(a)`.
    /// A contradiction surfaced by the exchange collapses to ⊥.
    #[inline]
    pub fn reduce(&self, w: u32) -> Self {
        if self.is_bottom() {
            return BitsCong::bottom();
        }
        // kb → cong: 2-adic residue from the known low prefix.
        let k = self.kb.trailing_known(w);
        let kb_cong = if k == 0 {
            Cong::top()
        } else {
            // cap modulus exponent at 63 to keep `1 << j` representable.
            let j = k.min(63);
            Cong::new(1u64 << j, self.kb.low_bits_value(j))
        };
        let cong1 = self.cong.meet(&kb_cong);

        // cong → kb: fix low v2(m) bits from the residue.
        let kb_from_cong = match cong1 {
            Cong::Bottom => KnownBits::Bottom,
            Cong::Mod { m, r } => {
                let j = m.trailing_zeros().min(w).min(63);
                if j == 0 {
                    KnownBits::top()
                } else {
                    let low_mask = (1u64 << j) - 1;
                    let low_r = r & low_mask;
                    // low j bits fixed to low_r: ones = low_r, zeros = !low_r & low_mask
                    KnownBits::new(!low_r & low_mask, low_r, w)
                }
            }
        };
        let kb1 = self.kb.meet(&kb_from_cong, w);

        if matches!(kb1, KnownBits::Bottom) || matches!(cong1, Cong::Bottom) {
            return BitsCong::bottom();
        }
        BitsCong {
            kb: kb1,
            cong: cong1,
        }
    }

    // ── transfers ──

    /// Bitwise AND. Known-bits is exact; the congruence is recovered by
    /// reduction from the resulting low known bits.
    #[inline]
    pub fn and(&self, other: &Self, w: u32) -> Self {
        let kb = match (self.kb, other.kb) {
            (KnownBits::Bottom, _) | (_, KnownBits::Bottom) => KnownBits::Bottom,
            (
                KnownBits::Bits {
                    zeros: z1,
                    ones: o1,
                },
                KnownBits::Bits {
                    zeros: z2,
                    ones: o2,
                },
            ) => KnownBits::new(z1 | z2, o1 & o2, w),
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// Bitwise OR.
    #[inline]
    pub fn or(&self, other: &Self, w: u32) -> Self {
        let kb = match (self.kb, other.kb) {
            (KnownBits::Bottom, _) | (_, KnownBits::Bottom) => KnownBits::Bottom,
            (
                KnownBits::Bits {
                    zeros: z1,
                    ones: o1,
                },
                KnownBits::Bits {
                    zeros: z2,
                    ones: o2,
                },
            ) => KnownBits::new(z1 & z2, o1 | o2, w),
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// Bitwise XOR.
    #[inline]
    pub fn xor(&self, other: &Self, w: u32) -> Self {
        let kb = match (self.kb, other.kb) {
            (KnownBits::Bottom, _) | (_, KnownBits::Bottom) => KnownBits::Bottom,
            (
                KnownBits::Bits {
                    zeros: z1,
                    ones: o1,
                },
                KnownBits::Bits {
                    zeros: z2,
                    ones: o2,
                },
            ) => {
                let known = (z1 | o1) & (z2 | o2);
                let val = (o1 ^ o2) & known;
                KnownBits::new(known & !val, val, w)
            }
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// Bitwise NOT (`x ^ all-ones`).
    #[inline]
    pub fn not(&self, w: u32) -> Self {
        let kb = match self.kb {
            KnownBits::Bottom => KnownBits::Bottom,
            KnownBits::Bits { zeros, ones } => KnownBits::new(ones, zeros, w),
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// Logical left shift by a constant `s`.
    #[inline]
    pub fn shl(&self, s: u32, w: u32) -> Self {
        if s >= w {
            return BitsCong::constant(0, w);
        }
        let kb = match self.kb {
            KnownBits::Bottom => KnownBits::Bottom,
            KnownBits::Bits { zeros, ones } => {
                let low_zeros = (1u64 << s) - 1; // shifted-in low bits are 0
                KnownBits::new((zeros << s) | low_zeros, ones << s, w)
            }
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// Logical (unsigned) right shift by a constant `s`.
    #[inline]
    pub fn shr_u(&self, s: u32, w: u32) -> Self {
        if s >= w {
            return BitsCong::constant(0, w);
        }
        let kb = match self.kb {
            KnownBits::Bottom => KnownBits::Bottom,
            KnownBits::Bits { zeros, ones } => {
                // top `s` bits become known-0.
                let mask = width_mask(w);
                let high_zeros = mask & !(mask >> s);
                KnownBits::new((zeros >> s) | high_zeros, ones >> s, w)
            }
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// Arithmetic (signed) right shift by a constant `s`. The top `s` bits are
    /// filled with the sign bit (bit `w-1`); if it is unknown they stay
    /// unknown.
    #[inline]
    pub fn shr_s(&self, s: u32, w: u32) -> Self {
        if s == 0 {
            return *self;
        }
        let kb = match self.kb {
            KnownBits::Bottom => KnownBits::Bottom,
            KnownBits::Bits { zeros, ones } => {
                let mask = width_mask(w);
                let sign = 1u64 << (w - 1);
                let high_mask = mask & !(mask >> s); // the top s positions
                let s_eff = s.min(w);
                let mut z = (zeros >> s_eff) & mask;
                let mut o = (ones >> s_eff) & mask;
                if zeros & sign != 0 {
                    // sign known 0 ⇒ fill high bits with 0
                    z |= high_mask;
                } else if ones & sign != 0 {
                    // sign known 1 ⇒ fill high bits with 1
                    o |= high_mask;
                }
                KnownBits::new(z, o, w)
            }
        };
        BitsCong {
            kb,
            cong: Cong::top(),
        }
        .reduce(w)
    }

    /// `x + y` (wrapping at width `w`). `wrap_free` is the analyzer's no-wrap
    /// proof (from the interval domain).
    #[inline]
    pub fn add(&self, other: &Self, w: u32, wrap_free: bool) -> Self {
        let kb = add_known_bits(&self.kb, &other.kb, w);
        let cong = cong_add(&self.cong, &other.cong, w, wrap_free);
        BitsCong { kb, cong }.reduce(w)
    }

    /// `x - y` (wrapping at width `w`).
    #[inline]
    pub fn sub(&self, other: &Self, w: u32, wrap_free: bool) -> Self {
        // Known-bits for subtraction: only the common trailing known bits
        // survive (a borrow cannot reach below the lowest unknown position).
        let kb = sub_known_bits(&self.kb, &other.kb, w);
        let cong = cong_sub(&self.cong, &other.cong, w, wrap_free);
        BitsCong { kb, cong }.reduce(w)
    }

    /// `x * y` (wrapping at width `w`).
    #[inline]
    pub fn mul(&self, other: &Self, w: u32, wrap_free: bool) -> Self {
        let kb = mul_known_bits(&self.kb, &other.kb, w);
        let cong = cong_mul(&self.cong, &other.cong, w, wrap_free);
        BitsCong { kb, cong }.reduce(w)
    }
}

// ── known-bits arithmetic helpers (sound trailing-bit rules) ──

/// Trailing-known length and low value, or `None` for ⊥.
#[inline]
fn tk(kb: &KnownBits, w: u32) -> Option<(u32, u64)> {
    match kb {
        KnownBits::Bottom => None,
        _ => {
            let k = kb.trailing_known(w);
            Some((k, kb.low_bits_value(k.min(63))))
        }
    }
}

/// Known-bits transfer for `x + y`: the low `j = min(tk a, tk b)` bits of the
/// sum are determined (carry within a fully-known low prefix is itself known);
/// bit `j` and above are unknown. Sound (LLVM computes more, this never claims
/// a bit it cannot prove).
#[inline]
fn add_known_bits(a: &KnownBits, b: &KnownBits, w: u32) -> KnownBits {
    let (Some((ka, va)), Some((kb, vb))) = (tk(a, w), tk(b, w)) else {
        return KnownBits::Bottom;
    };
    // Cap at 63: `va`/`vb` only carry the low 63 known bits (see `tk`), so we
    // must not claim bit 63. The congruence singleton carries full exactness
    // for 64-bit constants.
    let j = ka.min(kb).min(w).min(63);
    if j == 0 {
        return KnownBits::top();
    }
    let low_mask = (1u64 << j) - 1;
    let low = va.wrapping_add(vb) & low_mask;
    KnownBits::new(!low & low_mask, low, w)
}

/// Known-bits transfer for `x - y`: same trailing-prefix reasoning (a borrow
/// cannot cross a fully-known low prefix).
#[inline]
fn sub_known_bits(a: &KnownBits, b: &KnownBits, w: u32) -> KnownBits {
    let (Some((ka, va)), Some((kb, vb))) = (tk(a, w), tk(b, w)) else {
        return KnownBits::Bottom;
    };
    let j = ka.min(kb).min(w).min(63);
    if j == 0 {
        return KnownBits::top();
    }
    let low_mask = (1u64 << j) - 1;
    let low = va.wrapping_sub(vb) & low_mask;
    KnownBits::new(!low & low_mask, low, w)
}

/// Known-bits transfer for `x * y`: trailing zeros add — if `x` has `ta` known
/// trailing zeros and `y` has `tb`, the product has at least `ta + tb` known
/// trailing zeros (alignment). Sound; other bits left ⊤.
#[inline]
fn mul_known_bits(a: &KnownBits, b: &KnownBits, w: u32) -> KnownBits {
    let (ta, tb) = match (a, b) {
        (KnownBits::Bottom, _) | (_, KnownBits::Bottom) => return KnownBits::Bottom,
        _ => (trailing_zeros_known(a, w), trailing_zeros_known(b, w)),
    };
    let t = (ta + tb).min(w);
    if t == 0 {
        return KnownBits::top();
    }
    let zeros = if t >= 64 { u64::MAX } else { (1u64 << t) - 1 };
    KnownBits::new(zeros, 0, w)
}

/// Number of contiguous low bits known to be **zero**, capped at `w`.
#[inline]
fn trailing_zeros_known(kb: &KnownBits, w: u32) -> u32 {
    match kb {
        KnownBits::Bottom => w,
        KnownBits::Bits { zeros, .. } => {
            let z = zeros & width_mask(w);
            // first bit not known-zero = first 0 in `z`.
            (!z).trailing_zeros().min(w)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    extern crate alloc;
    use alloc::vec::Vec;

    const W: u32 = 8; // exhaustive concrete domain [0, 256)

    /// α: abstract a concrete set as the join of its singletons (the most
    /// precise sound abstraction reachable by `join` of constants).
    fn alpha(set: &[u64]) -> BitsCong {
        set.iter().fold(BitsCong::bottom(), |acc, &x| {
            acc.join(&BitsCong::constant(x, W), W)
        })
    }

    // ── known-bits γ-soundness of α and the lattice laws ──

    #[test]
    fn alpha_contains_its_witnesses() {
        for chunk in [
            vec![0u64],
            vec![8, 16, 24, 32],
            vec![3, 7, 11, 15],
            vec![0, 255],
            (0u64..256).step_by(4).collect::<Vec<_>>(),
        ] {
            let a = alpha(&chunk);
            for &x in &chunk {
                assert!(
                    a.contains(x, W),
                    "α({chunk:?}) must contain its witness {x}"
                );
            }
        }
    }

    #[test]
    fn join_over_approximates_union() {
        let xs = [4u64, 12, 20];
        let ys = [6u64, 10];
        let a = alpha(&xs);
        let b = alpha(&ys);
        let j = a.join(&b, W);
        for &x in xs.iter().chain(ys.iter()) {
            assert!(j.contains(x, W), "join must contain {x}");
        }
    }

    #[test]
    fn leq_is_consistent_with_gamma() {
        // a ⊑ b ⇒ γ(a) ⊆ γ(b), checked exhaustively.
        let samples = [
            alpha(&[8, 16, 24]),
            alpha(&[8, 16, 24, 40]),
            alpha(&[0]),
            BitsCong::top(),
            alpha(&[3, 7]),
        ];
        for a in &samples {
            for b in &samples {
                if a.leq(b) {
                    for x in 0u64..256 {
                        if a.contains(x, W) {
                            assert!(b.contains(x, W), "a⊑b but {x} ∈ γ(a)∖γ(b): a={a:?} b={b:?}");
                        }
                    }
                }
            }
        }
    }

    // ── transfer soundness: exhaustive γ-sweep over [0,256)² ──

    /// For a binary op, assert: for all concrete x∈γ(α(xs)), y∈γ(α(ys)), the
    /// concrete (wrapping) result is in γ(transfer#(α(xs), α(ys))).
    fn sweep_binary(
        xs: &[u64],
        ys: &[u64],
        transfer: impl Fn(&BitsCong, &BitsCong) -> BitsCong,
        concrete: impl Fn(u64, u64) -> u64,
    ) {
        let a = alpha(xs);
        let b = alpha(ys);
        let r = transfer(&a, &b);
        // sweep the FULL concretizations (not just the witnesses) — this is the
        // real soundness obligation.
        for x in 0u64..256 {
            if !a.contains(x, W) {
                continue;
            }
            for y in 0u64..256 {
                if !b.contains(y, W) {
                    continue;
                }
                let z = concrete(x, y) & width_mask(W);
                assert!(
                    r.contains(z, W),
                    "transfer unsound: {x} op {y} = {z} ∉ γ(result={r:?}); a={a:?} b={b:?}"
                );
            }
        }
    }

    #[test]
    fn and_sound() {
        sweep_binary(
            &[0xF0, 0xF8],
            &[0x0F, 0x1F],
            |a, b| a.and(b, W),
            |x, y| x & y,
        );
    }
    #[test]
    fn or_sound() {
        sweep_binary(
            &[0xF0, 0x80],
            &[0x0F, 0x01],
            |a, b| a.or(b, W),
            |x, y| x | y,
        );
    }
    #[test]
    fn xor_sound() {
        sweep_binary(
            &[0xFF, 0xF0],
            &[0x0F, 0x33],
            |a, b| a.xor(b, W),
            |x, y| x ^ y,
        );
    }

    #[test]
    fn add_wrapping_sound() {
        // wrap_free = false — must stay sound even when the sum wraps past 256.
        sweep_binary(
            &[200, 208, 216], // ≡ 0 (mod 8), large enough to wrap
            &[100, 108],
            |a, b| a.add(b, W, false),
            |x, y| x.wrapping_add(y),
        );
    }

    #[test]
    fn sub_wrapping_sound() {
        sweep_binary(
            &[4, 12, 20],
            &[8, 16],
            |a, b| a.sub(b, W, false),
            |x, y| x.wrapping_sub(y),
        );
    }

    #[test]
    fn mul_wrapping_sound() {
        sweep_binary(
            &[4, 8, 12], // ≡ 0 (mod 4)
            &[6, 10],    // ≡ 0 (mod 2)
            |a, b| a.mul(b, W, false),
            |x, y| x.wrapping_mul(y),
        );
    }

    #[test]
    fn shifts_sound() {
        for xs in [vec![0xF0u64, 0xF8], vec![3, 7, 11], vec![0x81, 0xC0]] {
            let a = alpha(&xs);
            for s in 0u32..W {
                let shl = a.shl(s, W);
                let shru = a.shr_u(s, W);
                for x in 0u64..256 {
                    if !a.contains(x, W) {
                        continue;
                    }
                    let l = (x << s) & width_mask(W);
                    assert!(shl.contains(l, W), "shl unsound: {x}<<{s}={l} ∉ {shl:?}");
                    let r = (x & width_mask(W)) >> s;
                    assert!(
                        shru.contains(r, W),
                        "shr_u unsound: {x}>>{s}={r} ∉ {shru:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn not_sound() {
        let a = alpha(&[0xF0, 0x0F, 0xAA]);
        let n = a.not(W);
        for x in 0u64..256 {
            if a.contains(x, W) {
                let nx = (!x) & width_mask(W);
                assert!(n.contains(nx, W), "not unsound: !{x}={nx} ∉ {n:?}");
            }
        }
    }

    // ── the wrapping-soundness subtlety, made concrete ──

    #[test]
    fn nonpow2_modulus_weakens_under_possible_wrap() {
        // x ≡ 2 (mod 3): {2,5,8,...}. Add x to itself with wrap possible.
        let xs: Vec<u64> = (0u64..256).filter(|v| v % 3 == 2).collect();
        let a = alpha(&xs);
        // sanity: α recovered the mod-3 fact.
        assert!(
            matches!(a.cong, Cong::Mod { m: 3, r: 2 }),
            "α should see ≡2 mod3, got {:?}",
            a.cong
        );
        // possible-wrap add ⇒ modulus must weaken to gcd(3, 256) = 1 (⊤),
        // and the result must still be sound over the wrapped domain.
        let r = a.add(&a, W, false);
        for &x in &xs {
            for &y in &xs {
                let z = x.wrapping_add(y) & width_mask(W);
                assert!(r.contains(z, W), "wrap-weakened add must contain {z}");
            }
        }
    }

    #[test]
    fn nonpow2_modulus_retained_when_wrap_free() {
        // Same values, but assert wrap_free: the analyzer proved no overflow.
        // Then the full mod-3 fact must survive: 2+2 ≡ 4 ≡ 1 (mod 3).
        let xs: Vec<u64> = (0u64..16).filter(|v| v % 3 == 2).collect(); // {2,5,8,11,14}
        let a = alpha(&xs);
        let r = a.add(&a, W, true);
        // every wrap-free sum is ≡ 1 (mod 3)
        match r.cong {
            Cong::Mod { m: 3, r: 1 } => {}
            other => panic!("wrap-free add should retain ≡1 mod3, got {other:?}"),
        }
        for &x in &xs {
            for &y in &xs {
                let z = x + y; // wrap-free by construction (≤ 28 < 256)
                assert!(r.contains(z, W), "wrap-free add must contain {z}");
            }
        }
    }

    // ── reduction: 2-adic exchange, γ-preserving ──

    #[test]
    fn reduction_preserves_gamma() {
        // start from a kb that fixes low 3 bits = 0; reduce must add ≡0 mod8.
        let bc = BitsCong {
            kb: KnownBits::new(0b111, 0, W),
            cong: Cong::top(),
        };
        let red = bc.reduce(W);
        assert!(
            matches!(red.cong, Cong::Mod { m: 8, r: 0 }),
            "got {:?}",
            red.cong
        );
        // γ unchanged: exactly the multiples of 8.
        for x in 0u64..256 {
            assert_eq!(
                bc.contains(x, W),
                red.contains(x, W),
                "reduction changed γ at {x}"
            );
        }
    }

    #[test]
    fn reduction_cong_to_bits() {
        // ≡ 4 (mod 8): low 3 bits fixed to 0b100.
        let bc = BitsCong {
            kb: KnownBits::top(),
            cong: Cong::new(8, 4),
        };
        let red = bc.reduce(W);
        // low 3 bits must now be known = 100.
        for x in 0u64..256 {
            assert_eq!(bc.contains(x, W), red.contains(x, W), "γ changed at {x}");
        }
        assert!(red.kb.contains(4, W) && red.kb.contains(12, W));
        assert!(!red.kb.contains(5, W), "low bits should exclude 5");
    }

    #[test]
    fn conflicting_meet_is_bottom() {
        let a = BitsCong {
            kb: KnownBits::new(0, 1, W),
            cong: Cong::top(),
        }; // bit0 = 1
        let b = BitsCong {
            kb: KnownBits::new(1, 0, W),
            cong: Cong::top(),
        }; // bit0 = 0
        let m = a.meet(&b, W);
        assert!(
            m.is_bottom(),
            "contradictory known bits must meet to ⊥, got {m:?}"
        );
    }

    /// Heavy exhaustive sweep: for every pair of residue classes (m1,r1),
    /// (m2,r2) over small moduli, abstract the class, run each arithmetic
    /// transfer with wrap_free=false, and assert soundness against every
    /// concrete pair. This is the real adversary for the wrapping logic.
    #[test]
    fn exhaustive_residue_class_arithmetic_is_sound() {
        let class =
            |m: u64, r: u64| -> Vec<u64> { (0u64..256).filter(|v| v % m == r % m).collect() };
        type Tf = fn(&BitsCong, &BitsCong) -> BitsCong;
        type Cf = fn(u64, u64) -> u64;
        let ops: [(Tf, Cf); 6] = [
            (|p, q| p.add(q, W, false), |x, y| x.wrapping_add(y)),
            (|p, q| p.sub(q, W, false), |x, y| x.wrapping_sub(y)),
            (|p, q| p.mul(q, W, false), |x, y| x.wrapping_mul(y)),
            (|p, q| p.and(q, W), |x, y| x & y),
            (|p, q| p.or(q, W), |x, y| x | y),
            (|p, q| p.xor(q, W), |x, y| x ^ y),
        ];
        for m1 in 1u64..=12 {
            for r1 in 0..m1 {
                for m2 in 1u64..=12 {
                    for r2 in 0..m2 {
                        let xs = class(m1, r1);
                        let ys = class(m2, r2);
                        let a = alpha(&xs);
                        let b = alpha(&ys);
                        for (tf, cf) in ops.iter() {
                            let r = tf(&a, &b);
                            for &x in &xs {
                                for &y in &ys {
                                    let z = cf(x, y) & width_mask(W);
                                    assert!(
                                        r.contains(z, W),
                                        "unsound: classes ({m1},{r1})×({m2},{r2}): {x},{y}->{z} ∉ {r:?}"
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
    fn gcd_with_pow2_is_two_adic() {
        assert_eq!(gcd_with_pow2(3, 8), 1);
        assert_eq!(gcd_with_pow2(12, 8), 4); // v2(12)=2
        assert_eq!(gcd_with_pow2(8, 8), 8);
        assert_eq!(gcd_with_pow2(8, 2), 4); // capped at 2^w
        assert_eq!(gcd_with_pow2(1, 8), 1);
    }
}
