import Project.ExpWide.Numerical
import Project.ExpSmall.Tail

namespace Project.ExpWide
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem reduction_tail (x : UInt64) (hf : Finite x)
    (hl : -16 ≤ value x) (hu : value x ≤ -8) :
    Finite (Wasm.IEEE64.div x 0x4020000000000000) ∧
    -2 ≤ value (Wasm.IEEE64.div x 0x4020000000000000) ∧
    value (Wasm.IEEE64.div x 0x4020000000000000) ≤ -999/1000 := by
  have hq : |value x / value 0x4020000000000000| ≤ 2 := by
    rw [eight_value]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := F64DivBounds.div_real_mixed x 0x4020000000000000 hf
    (by unfold CodeLib.IEEE64.Finite; decide)
    (by decide) (hq.trans_lt (by norm_num))
  have he : |value (Wasm.IEEE64.div x 0x4020000000000000) - value x / 8| ≤
      2*unitRoundoff64 + multiplicationUnderflowEpsilon := by
    rw [eight_value] at hs hq
    exact hs.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
  have heps : 2*unitRoundoff64+ multiplicationUnderflowEpsilon < 2*arithmeticEpsilon ∧
      2*arithmeticEpsilon ≤ 1/1000 := by
    norm_num [unitRoundoff64, multiplicationUnderflowEpsilon, arithmeticEpsilon]
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ 2 he (by simpa [eight_value] using hq)
  have hb := F64UnitInterval.abs_le_two_of_lt_successor
    (Wasm.IEEE64.div x 0x4020000000000000) (by linarith)
  have ha := (abs_le.mp he).2
  exact ⟨hs.1, (abs_le.mp hb).1, by linarith⟩

theorem evaluate_tail_bounds (x : UInt64) (hf : Finite x)
    (hl : -16 ≤ value x) (hu : value x ≤ -8) :
    Finite (evaluate x) ∧ 1/1000000000 ≤ value (evaluate x) ∧ value (evaluate x) ≤ 1/400 := by
  have hd := reduction_tail x hf hl hu
  have ha := ExpSmall.polynomial_tail_computed _ hd.1 hd.2.1 hd.2.2
  let a := ExpSmall.polynomial (Wasm.IEEE64.div x 0x4020000000000000)
  have h1 := F64Square.interval a (1/10) (46/100) ha.1 (by norm_num) ha.2.1 ha.2.2 (by norm_num)
  have hb : 1/101 ≤ value (Wasm.IEEE64.mul a a) ∧
      value (Wasm.IEEE64.mul a a) ≤ 212/1000 := by
    norm_num [arithmeticEpsilon] at h1
    constructor <;> linarith
  let b := Wasm.IEEE64.mul a a
  have h2 := F64Square.interval b (1/101) (212/1000) h1.1 (by norm_num) hb.1 hb.2 (by norm_num)
  have hc : 1/11000 ≤ value (Wasm.IEEE64.mul b b) ∧
      value (Wasm.IEEE64.mul b b) ≤ 45/1000 := by
    norm_num [arithmeticEpsilon] at h2
    constructor <;> linarith
  let c := Wasm.IEEE64.mul b b
  have h3 := F64Square.interval c (1/11000) (45/1000) h2.1 (by norm_num) hc.1 hc.2 (by norm_num)
  refine ⟨h3.1, ?_, ?_⟩
  · change 1/1000000000 ≤ value (Wasm.IEEE64.mul c c)
    norm_num [arithmeticEpsilon] at h3
    linarith [h3.2.1]
  · change value (Wasm.IEEE64.mul c c) ≤ 1/400
    norm_num [arithmeticEpsilon] at h3
    linarith [h3.2.2]

theorem exp_tail_upper (x : ℝ) (hx : x ≤ -8) : Real.exp x ≤ 1/400 := by
  have h := Real.sum_le_exp_of_nonneg (x := 8) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hb : 400 ≤ Real.exp 8 := by linarith
  have hm : Real.exp x*Real.exp 8 ≤ 1 := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show x+8 ≤ 0 by linarith)
  have hp := mul_le_mul_of_nonneg_left hb (Real.exp_pos x).le
  nlinarith

theorem evaluate_error_sixteen (x : UInt64) (hf : Finite x)
    (hl : -16 ≤ value x) (hu : value x ≤ 0) :
    Finite (evaluate x) ∧ 1/1000000000 ≤ value (evaluate x) ∧
    |value (evaluate x)-Real.exp (value x)| ≤ 1/400 := by
  by_cases hx : -8 ≤ value x
  · have h := evaluate_error x hf hx hu
    exact ⟨h.1, h.2.1.trans' (by norm_num), h.2.2⟩
  · have hb := evaluate_tail_bounds x hf hl (by linarith)
    have he := exp_tail_upper (value x) (by linarith)
    exact ⟨hb.1, hb.2.1, abs_le.mpr ⟨by linarith [Real.exp_pos (value x)],
      by linarith [Real.exp_pos (value x)]⟩⟩

#print axioms evaluate_error_sixteen
end Project.ExpWide
