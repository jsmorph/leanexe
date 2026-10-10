import LeanExe.ProofKit.F64Adjacent
import LeanExe.ProofKit.F64NearestNonnegative

namespace LeanExe.ProofKit.F64PositiveOrder
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem value_strict {left right : UInt64} (hr : right.toNat < 2 ^ 63)
    (hlt : left.toNat < right.toNat) : value left < value right := by
  have habs (w : UInt64) (hw : w.toNat < 2 ^ 63) : F64Order.absBits w = w := by
    apply UInt64.toNat_inj.mp
    rw [F64Order.absBits_toNat, Nat.mod_eq_of_lt hw]
  have hn (w : UInt64) (hw : w.toNat < 2 ^ 63) : 0 ≤ value w := by
    rw [F64Adjacent.unsigned_word_value w hw]
    positivity
  have hl := hlt.trans hr
  have hv := F64Order.abs_value_lt left right (by
    rw [habs left hl, habs right hr]
    exact UInt64.lt_iff_toNat_lt.mpr hlt)
  simpa only [abs_of_nonneg (hn left hl), abs_of_nonneg (hn right hr)] using hv

theorem value_le_iff {left right : UInt64}
    (hl : left.toNat < 2 ^ 63) (hr : right.toNat < 2 ^ 63) :
    value left ≤ value right ↔ left.toNat ≤ right.toNat := by
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) (value_strict hl (by omega))
  · intro h
    rcases h.eq_or_lt with h | h
    · have he : left = right := UInt64.toNat_inj.mp h
      subst right
      exact le_rfl
    · exact (value_strict hr h).le

theorem nearest_interval (y : ℝ) (w lo hi : UInt64)
    (hw : F64NearestNonnegative.Nearest y w)
    (hlo : lo.toNat < F64NearestNonnegative.limit)
    (hhi : hi.toNat < F64NearestNonnegative.limit)
    (hyl : value lo ≤ y) (hyh : y ≤ value hi) :
    lo.toNat ≤ w.toNat ∧ w.toNat ≤ hi.toNat := by
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  constructor
  · by_contra hn
    have hlt := value_strict (hlo.trans hlim) (show w.toNat < lo.toNat by omega)
    have hd := hw.2 lo hlo
    rw [abs_of_nonpos (by linarith : value w - y ≤ 0),
      abs_of_nonpos (by linarith : value lo - y ≤ 0)] at hd
    linarith
  · by_contra hn
    have hlt := value_strict (hw.1.trans hlim) (show hi.toNat < w.toNat by omega)
    have hd := hw.2 hi hhi
    rw [abs_of_nonneg (by linarith : 0 ≤ value w - y),
      abs_of_nonneg (by linarith : 0 ≤ value hi - y)] at hd
    linarith

theorem positive_finite_encoding (w : UInt64) (hf : CodeLib.IEEE64.Finite w)
    (hp : 0 < value w) : w.toNat < F64NearestNonnegative.limit := by
  have h := F64Order.positiveBits_of_finite_value_pos w hf hp
  simp only [F64Order.positiveBits, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact UInt64.lt_iff_toNat_lt.mp h.2

#print axioms positive_finite_encoding

#print axioms value_strict
#print axioms value_le_iff
#print axioms nearest_interval

end LeanExe.ProofKit.F64PositiveOrder
