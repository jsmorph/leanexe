import Library.Numerics.Float64.Exp.ExpCoreRange

namespace Library.Numerics.Float64.Exp.ExpCoreInterval
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem quotient_bounds (x : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 512)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) : -769 ≤ q ∧ q ≤ 768 := by
  obtain ⟨k', _, hscaled, habs⟩ := ExpScaleFacts.integer_small x hxf hx
  have hv : value (ExpReductionSelection.integer x) = (k' : ℝ) := by
    rw [value, hscaled]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have he : k' = k := by exact_mod_cast (hv.symm.trans hkv)
  subst k'
  have habi : (k.natAbs : Int) ≤ 98305 := by exact_mod_cast habs
  rw [← Int.abs_eq_natAbs] at habi
  have hab := abs_le.mp habi
  have hj := j.isLt
  omega

theorem nonzero_interval (x : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 512)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hj : j.val ≠ 0)
    (hs : value (ExpCoreState.scaleBits x) =
      (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) :
    (2 : ℝ) ^ q ≤ Real.exp (value x) ∧ Real.exp (value x) ≤ 2 * (2 : ℝ) ^ q ∧
    (2 : ℝ) ^ q ≤ value (ExpCoreBounds.core x) ∧
      value (ExpCoreBounds.core x) ≤ 2 * (2 : ℝ) ^ q ∧
    |value (ExpCoreBounds.core x) - Real.exp (value x)| <
      3 * unitRoundoff64 * (2 : ℝ) ^ q := by
  let P := (2 : ℝ) ^ q
  have hP : 0 < P := zpow_pos (by norm_num) _
  have hT := ExpCoreRange.target_binade x k q j hxf (hx.trans (by norm_num)) hkv hk hj
  have he := (ExpCoreBounds.core_error x hxf hx).2
  rw [hs] at he
  have hB : |value (ExpCoreBounds.core x) - Real.exp (value x)| ≤
      ((7 / 5) * (255 / 128) * unitRoundoff64) * P := by
    have hfactor : 0 ≤ (7 / 5) * unitRoundoff64 * P :=
      mul_nonneg (mul_nonneg (by norm_num) (by norm_num [unitRoundoff64])) hP.le
    have hm := mul_le_mul_of_nonneg_left (ExpCoreRange.head_bounds j).1 hfactor
    exact he.trans (by nlinarith only [hm])
  have hmargin : (7 / 5 : ℝ) * (255 / 128) * unitRoundoff64 ≤ 1 / 65536 := by
    norm_num [unitRoundoff64]
  have hm := hB.trans (mul_le_mul_of_nonneg_right hmargin hP.le)
  have he' := abs_le.mp hm
  have hstrict : ((7 / 5) * (255 / 128) * unitRoundoff64) * P <
      3 * unitRoundoff64 * P := by
    have hcoeff : (7 / 5 : ℝ) * (255 / 128) * unitRoundoff64 <
        3 * unitRoundoff64 := by norm_num [unitRoundoff64]
    exact mul_lt_mul_of_pos_right hcoeff hP
  refine ⟨?_, ?_, ?_, ?_, hB.trans_lt hstrict⟩
  all_goals dsimp [P] at *
  all_goals linarith

theorem zero_interval (x : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 512)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hj : j.val = 0)
    (hs : value (ExpCoreState.scaleBits x) =
      (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val)) :
    (2 : ℝ) ^ q / 2 ≤ Real.exp (value x) ∧
      Real.exp (value x) ≤ 2 * (2 : ℝ) ^ q ∧
    (2 : ℝ) ^ q / 2 ≤ value (ExpCoreBounds.core x) ∧
      value (ExpCoreBounds.core x) ≤ 2 * (2 : ℝ) ^ q ∧
    |value (ExpCoreBounds.core x) - Real.exp (value x)| <
      3 * (unitRoundoff64 * (2 : ℝ) ^ q) / 2 := by
  let P := (2 : ℝ) ^ q
  have hP : 0 < P := zpow_pos (by norm_num) _
  have hs' : value (ExpCoreState.scaleBits x) = P := by
    rw [hs, hj, ExpCoreRange.zero_entry.1, mul_one]
  have htarget : Real.exp (value x) = P * Real.exp (ExpResidualBounds.ideal x) := by
    rw [ExpCoreRange.target_factor x k q j hkv hk, hj]
    simp only [Nat.cast_zero, zero_mul, zero_div, Real.exp_zero, mul_one]
    rfl
  have ha := ExpCoreRange.ideal_exponential_range x hxf (hx.trans (by norm_num))
  have hElo : P * (319 / 320) ≤ Real.exp (value x) := by
    rw [htarget]
    exact mul_le_mul_of_nonneg_left ha.1 hP.le
  have hEhi : Real.exp (value x) ≤ P * (257 / 256) := by
    rw [htarget]
    exact mul_le_mul_of_nonneg_left ha.2 hP.le
  have he := (ExpCoreBounds.core_error x hxf hx).2
  rw [hs'] at he
  have hmargin : (7 / 5 : ℝ) * unitRoundoff64 ≤ 1 / 256 := by norm_num [unitRoundoff64]
  have hm : |value (ExpCoreBounds.core x) - Real.exp (value x)| ≤ P / 256 :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_right hmargin hP.le])
  have he' := abs_le.mp hm
  have hstrict : (7 / 5) * unitRoundoff64 * P < 3 * (unitRoundoff64 * P) / 2 := by
    have hcoeff : (7 / 5 : ℝ) * unitRoundoff64 < 3 * unitRoundoff64 / 2 := by
      norm_num [unitRoundoff64]
    nlinarith only [mul_lt_mul_of_pos_right hcoeff hP]
  refine ⟨?_, ?_, ?_, ?_, he.trans_lt hstrict⟩
  all_goals dsimp [P] at *
  all_goals linarith

#print axioms quotient_bounds
#print axioms nonzero_interval
#print axioms zero_interval

end Library.Numerics.Float64.Exp.ExpCoreInterval
