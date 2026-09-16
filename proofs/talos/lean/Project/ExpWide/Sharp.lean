import Project.ExpWide.Tail
import Project.ExpSmall.PowerBound

namespace Project.ExpWide
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem reduction_sixteen (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 16) :
    Finite (Wasm.IEEE64.div x 0x4020000000000000) ∧
    |value (Wasm.IEEE64.div x 0x4020000000000000)| ≤ 2 ∧
    |value (Wasm.IEEE64.div x 0x4020000000000000)-value x/8| ≤ 2*arithmeticEpsilon := by
  have hq : |value x/value 0x4020000000000000| ≤ 2 := by
    rw [eight_value, abs_div]
    norm_num
    linarith
  have hs := F64DivBounds.div_real_mixed x 0x4020000000000000 hf
    (by unfold CodeLib.IEEE64.Finite; decide) (by decide) (hq.trans_lt (by norm_num))
  have he : |value (Wasm.IEEE64.div x 0x4020000000000000)-value x/8| ≤
      2*unitRoundoff64+multiplicationUnderflowEpsilon := by
    rw [eight_value] at hs hq
    exact hs.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
  have heps : 2*unitRoundoff64+multiplicationUnderflowEpsilon < 2*arithmeticEpsilon := by
    norm_num [unitRoundoff64, multiplicationUnderflowEpsilon, arithmeticEpsilon]
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ 2 he
    (by simpa [eight_value] using hq)
  exact ⟨hs.1, F64UnitInterval.abs_le_two_of_lt_successor _ (by linarith), he.trans heps.le⟩

theorem reduced_polynomial_sharp (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 16) :
    Finite (ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000)) ∧
    |value (ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000))-
      ExpSmall.polynomialReal (value x/8)| ≤ 1/10000000000 := by
  have hr := reduction_sixteen x hf hx
  have hp := ExpSmall.polynomial_roundoff_two _ hr.1 hr.2.1
  have hq : |value x/8| ≤ 2 := by rw [abs_div]; norm_num; linarith
  have hl := ExpSmall.polynomial_lipschitz_two _ _ hr.2.1 hq
  have he : |ExpSmall.polynomialReal (value (Wasm.IEEE64.div x 0x4020000000000000))-
      ExpSmall.polynomialReal (value x/8)| ≤ 16*arithmeticEpsilon :=
    hl.trans (by linarith [hr.2.2])
  refine ⟨hp.1, (abs_sub_le _ _ _).trans ((add_le_add hp.2 he).trans ?_)⟩
  norm_num [arithmeticEpsilon]

theorem evaluate_error_sharp (x : UInt64) (hf : Finite x)
    (hl : -16 ≤ value x) (hu : value x ≤ 0) :
    Finite (evaluate x) ∧ 1/1000000000 ≤ value (evaluate x) ∧
    |value (evaluate x)-Real.exp (value x)| ≤ 1/300000 := by
  let a := ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000)
  let r := ExpSmall.polynomialReal (value x/8)
  have ht : 0 ≤ -value x/8 ∧ -value x/8 ≤ 2 := ⟨by linarith, by linarith⟩
  have hn : -(-value x/8) = value x/8 := by ring
  have hb := ExpSmall.polynomial_negative_bounds _ ht.1 ht.2
  have hp := ExpSmall.polynomial_negative_remainder _ ht.1
  rw [hn] at hb hp
  have hbase := ExpSmall.exp_negative_unit_bounds (-1) (by norm_num) (by norm_num)
  have he2 : (1:ℝ)/9 ≤ Real.exp (-2) := by
    have hid : Real.exp (-1)^2 = Real.exp (-2) := by rw [sq, ← Real.exp_add]; norm_num
    nlinarith [sq_nonneg (Real.exp (-1)-1/3)]
  have he := Real.exp_le_exp.mpr (show (-2:ℝ) ≤ value x/8 by linarith)
  have hr : 1/9 ≤ r := by dsimp [r]; linarith [hp.1]
  have h0 := reduced_polynomial_sharp x hf (abs_le.mpr ⟨hl, by linarith⟩)
  have ha : 1/10 ≤ value a := by
    have hh := (abs_le.mp h0.2).1
    change -(1/10000000000:ℝ) ≤ value a-r at hh
    linarith
  have h1 := F64Square.approximation a r (1/10000000000) (1/10) h0.1 hb h0.2
    (by norm_num) (by norm_num) ha
  have hl1 : 1/101 ≤ value (Wasm.IEEE64.mul a a) :=
    h1.2.1.trans' (by norm_num [arithmeticEpsilon])
  have he1 : |value (Wasm.IEEE64.mul a a)-r^2| ≤ 3/10000000000 :=
    h1.2.2.trans (by norm_num [arithmeticEpsilon])
  have hb1 : 0 ≤ r^2 ∧ r^2 ≤ 1 := ⟨sq_nonneg _, by nlinarith [hb.1, hb.2]⟩
  let b := Wasm.IEEE64.mul a a
  have h2 := F64Square.approximation b (r^2) (3/10000000000) (1/101) h1.1 hb1 he1
    (by norm_num) (by norm_num) hl1
  have hl2 : 1/11000 ≤ value (Wasm.IEEE64.mul b b) :=
    h2.2.1.trans' (by norm_num [arithmeticEpsilon])
  have he2 : |value (Wasm.IEEE64.mul b b)-(r^2)^2| ≤ 7/10000000000 :=
    h2.2.2.trans (by norm_num [arithmeticEpsilon])
  have hb2 : 0 ≤ (r^2)^2 ∧ (r^2)^2 ≤ 1 := ⟨sq_nonneg _, by nlinarith [hb1.2]⟩
  let c := Wasm.IEEE64.mul b b
  have h3 := F64Square.approximation c ((r^2)^2) (7/10000000000) (1/11000) h2.1 hb2 he2
    (by norm_num) (by norm_num) hl2
  have herr : |value (evaluate x)-r^8| ≤ 15/10000000000 := by
    change |value (Wasm.IEEE64.mul c c)-r^8| ≤ _
    rw [show r^8 = ((r^2)^2)^2 by ring]
    exact h3.2.2.trans (by norm_num [arithmeticEpsilon])
  have hp8 := ExpSmall.polynomial_eighth_error _ ht.1 ht.2
  rw [hn, show -8*(-value x/8) = value x by ring] at hp8
  refine ⟨h3.1, h3.2.1.trans' (by norm_num [arithmeticEpsilon]), ?_⟩
  exact (abs_sub_le _ _ _).trans ((add_le_add herr hp8).trans (by norm_num))

#print axioms evaluate_error_sharp
end Project.ExpWide
