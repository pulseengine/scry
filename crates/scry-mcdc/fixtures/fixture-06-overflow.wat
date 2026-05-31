;; fixture-06-overflow — MC/DC gap-closure inputs for the interval transfer
;; functions' straddle→TOP guard `lo < i32::MIN || hi > i32::MAX`
;; (scry-interval i32_add / i32_sub / i32_mul). The rest of the corpus uses
;; small constants, so that OR-decision is only ever evaluated (F,F) — the
;; non-overflow case. These functions drive each condition's TRUE polarity so
;; witness can form the independent-effect pair:
;;   *_ovf : hi > i32::MAX  (c1 = T, c0 = F)
;;   *_unf : lo < i32::MIN  (c0 = T, c1 = F)
;; Combined with the (F,F) vectors the small-constant fixtures already give,
;; this yields the (F,F)/(T,F)/(F,T) triple MC/DC needs for the OR.
(module
  ;; 2e9 + 2e9 = 4e9 > i32::MAX  → straddle hi>MAX true, lo<MIN false
  (func (export "add_ovf") (result i32)
    i32.const 2000000000
    i32.const 2000000000
    i32.add)
  ;; -2e9 + -2e9 = -4e9 < i32::MIN → straddle lo<MIN true, hi>MAX false
  (func (export "add_unf") (result i32)
    i32.const -2000000000
    i32.const -2000000000
    i32.add)
  ;; 2e9 - (-2e9) = 4e9 > i32::MAX → straddle hi>MAX true
  (func (export "sub_ovf") (result i32)
    i32.const 2000000000
    i32.const -2000000000
    i32.sub)
  ;; -2e9 - 2e9 = -4e9 < i32::MIN → straddle lo<MIN true
  (func (export "sub_unf") (result i32)
    i32.const -2000000000
    i32.const 2000000000
    i32.sub)
  ;; 1e5 * 1e5 = 1e10 > i32::MAX → straddle hi>MAX true
  (func (export "mul_ovf") (result i32)
    i32.const 100000
    i32.const 100000
    i32.mul)
  ;; 1e5 * -1e5 = -1e10 < i32::MIN → straddle lo<MIN true
  (func (export "mul_unf") (result i32)
    i32.const 100000
    i32.const -100000
    i32.mul))
