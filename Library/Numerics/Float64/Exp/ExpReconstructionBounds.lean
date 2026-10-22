import Library.Numerics.Float64.Exp.ExpEvaluationFloat

namespace Library.Numerics.Float64.Exp.ExpReconstructionBounds
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def reconstruction (s r t : UInt64) : UInt64 :=
  Wasm.IEEE64.add s (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t))

def floatReconstruction (s r t : Float) : Float :=
  s + s * ExpEvaluationBounds.floatEvaluation r t

theorem reconstruction_bits (s r t : Float) :
    (floatReconstruction s r t).toBits = reconstruction s.toBits r.toBits t.toBits := by
  simp only [floatReconstruction, reconstruction, F64Bits.toBits_add, F64Bits.toBits_mul,
    ExpEvaluationBounds.evaluation_bits]

/-- The sum before the final rounding of the reconstruction: the product `s · w` of the scale and
the evaluation is finite and at most `s / 32`, and `s + s · w` is within `(37/128) u s` of
`s (1 + t) exp r`. -/
theorem presum_error (s r t : UInt64)
    (hsf : Finite s) (hrf : Finite r) (htf : Finite t)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000)
    (hr : |value r| ≤ 1 / 256) (ht : |value t| ≤ 1 / (2 : ℝ) ^ 53) :
    Finite (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t)) ∧
    |value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t))| ≤ value s / 32 ∧
    |value s + value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t)) -
        value s * (1 + value t) * Real.exp (value r)| ≤
      (37 / 128) * unitRoundoff64 * value s := by
  let S := value s
  let T := value t
  let w := ExpEvaluationBounds.evaluation r t
  let W := value w
  let p := Wasm.IEEE64.mul s w
  let P := value p
  let I := T + Real.exp (value r) - 1
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have huhi : unitRoundoff64 ≤ (1 / 2 : ℝ) := by norm_num [unitRoundoff64]
  have hw := ExpEvaluationBounds.evaluation_error r t hrf htf hr ht
  have hwe := ExpEvaluationBounds.evaluation_exp_error r t hrf htf hr ht
  have hprod : |S * W| ≤ S / 64 := by
    rw [abs_mul, abs_of_pos hS]
    calc
      _ ≤ S * (1 / 64) := mul_le_mul_of_nonneg_left hw.2.1 hS.le
      _ = S / 64 := by ring
  have hprodMax : |S * W| < (2 : ℝ) ^ 1022 := by
    calc
      _ ≤ S / 64 := hprod
      _ ≤ (2 : ℝ) ^ 1000 / 64 := div_le_div_of_nonneg_right hshi (by norm_num)
      _ < (2 : ℝ) ^ 1022 := by norm_num
  have hm := F64MulBounds.mul_real_mixed s w hsf hw.1 hprodMax
  have hbeta : multiplicationUnderflowEpsilon ≤ unitRoundoff64 * S / 64 := by
    calc
      _ ≤ unitRoundoff64 * (1 / (2 : ℝ) ^ 1000) / 64 := by
        norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
      _ ≤ unitRoundoff64 * S / 64 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hslo hu) (by norm_num)
  have hme : |P - S * W| ≤ unitRoundoff64 * S / 32 := by
    calc
      _ ≤ unitRoundoff64 * |S * W| + multiplicationUnderflowEpsilon := hm.2
      _ ≤ unitRoundoff64 * (S / 64) + unitRoundoff64 * S / 64 :=
        add_le_add (mul_le_mul_of_nonneg_left hprod hu) hbeta
      _ = unitRoundoff64 * S / 32 := by ring
  have hPm : |P| ≤ S / 32 := by
    calc
      _ ≤ S / 64 + unitRoundoff64 * S / 32 :=
        F64ArithmeticBounds.magnitude_of_error _ _ _ _ hme hprod
      _ ≤ S / 32 := by
        nlinarith only [mul_le_mul_of_nonneg_right huhi hS.le]
  have hinner : |S + P - (S + S * I)| ≤
      unitRoundoff64 * S / 32 + S * (1 / (2 : ℝ) ^ 55) := by
    calc
      _ = |(P - S * W) + S * (W - I)| := by congr 1; ring
      _ ≤ |P - S * W| + |S * (W - I)| := abs_add_le _ _
      _ = |P - S * W| + S * |W - I| := by rw [abs_mul, abs_of_pos hS]
      _ ≤ unitRoundoff64 * S / 32 + S * (1 / (2 : ℝ) ^ 55) :=
        add_le_add hme (mul_le_mul_of_nonneg_left hwe hS.le)
  have hexp : |Real.exp (value r) - 1| ≤ (1 / 128 : ℝ) := by
    have he := Real.exp_bound (hr.trans (by norm_num)) (n := 1) (by decide)
    norm_num [Finset.sum_range_succ] at he
    linarith
  have ht' : |T| ≤ unitRoundoff64 := by simpa [unitRoundoff64] using ht
  have hcross : |(S + S * I) - S * (1 + T) * Real.exp (value r)| ≤
      S * (unitRoundoff64 / 128) := by
    calc
      _ = |S * T * (Real.exp (value r) - 1)| := by
        rw [show (S + S * I) - S * (1 + T) * Real.exp (value r) =
          -(S * T * (Real.exp (value r) - 1)) by dsimp [I]; ring, abs_neg]
      _ = S * |T| * |Real.exp (value r) - 1| := by
        rw [abs_mul, abs_mul, abs_of_pos hS]
      _ ≤ S * unitRoundoff64 * (1 / 128) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht' hS.le) hexp (abs_nonneg _)
          (mul_nonneg hS.le hu)
      _ = S * (unitRoundoff64 / 128) := by ring
  have hbetween :
      |S + P - S * (1 + T) * Real.exp (value r)| ≤
        (unitRoundoff64 * S / 32 + S * (1 / (2 : ℝ) ^ 55)) +
          S * (unitRoundoff64 / 128) :=
    (abs_sub_le _ (S + S * I) _).trans (add_le_add hinner hcross)
  refine ⟨hm.1, hPm, hbetween.trans (le_of_eq ?_)⟩
  norm_num [unitRoundoff64]
  ring

theorem reconstruction_error (s r t : UInt64)
    (hsf : Finite s) (hrf : Finite r) (htf : Finite t)
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000)
    (hr : |value r| ≤ 1 / 256) (ht : |value t| ≤ 1 / (2 : ℝ) ^ 53) :
    Finite (reconstruction s r t) ∧
    |value (reconstruction s r t) -
        value s * (1 + value t) * Real.exp (value r)| ≤
      (4 / 3) * unitRoundoff64 * value s := by
  obtain ⟨hpf, hPm, hbetween⟩ := presum_error s r t hsf hrf htf hslo hshi hr ht
  let S := value s
  let p := Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation r t)
  let P := value p
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hslo
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hsum : |S + P| ≤ (33 / 32) * S := by
    calc
      _ ≤ S + |P| := by simpa only [abs_of_pos hS] using abs_add_le S P
      _ ≤ S + S / 32 := add_le_add le_rfl hPm
      _ = (33 / 32) * S := by ring
  have hsumMax : |S + P| < (2 : ℝ) ^ 1023 := by
    calc
      _ ≤ (33 / 32) * S := hsum
      _ ≤ (33 / 32) * (2 : ℝ) ^ 1000 :=
        mul_le_mul_of_nonneg_left hshi (by norm_num)
      _ < (2 : ℝ) ^ 1023 := by norm_num
  have ha := F64AddBounds.add_real_relative s p hsf hpf hsumMax
  have hae : |value (Wasm.IEEE64.add s p) - (S + P)| ≤
      unitRoundoff64 * ((33 / 32) * S) :=
    ha.2.trans (mul_le_mul_of_nonneg_left hsum hu)
  refine ⟨ha.1, ?_⟩
  calc
    _ ≤ unitRoundoff64 * ((33 / 32) * S) + (37 / 128) * unitRoundoff64 * S :=
      (abs_sub_le _ (S + P) _).trans (add_le_add hae hbetween)
    _ = (169 / 128) * unitRoundoff64 * S := by ring
    _ ≤ (4 / 3) * unitRoundoff64 * S := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (169 / 128 : ℝ) ≤ 4 / 3) hu) hS.le

#print axioms reconstruction_bits
#print axioms presum_error
#print axioms reconstruction_error

end Library.Numerics.Float64.Exp.ExpReconstructionBounds
