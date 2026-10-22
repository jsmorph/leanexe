import Library.Numerics.Float64.Tanh.TanhBranches
import Library.Numerics.Float64.Tanh.Expm1Near
import LeanExe.ProofKit.F64NearestDiv
import LeanExe.ProofKit.F64NearestRelative

/-!
Facts for fdlibm's `tanh`: the absolute value and the doubled argument on words, the forms
`tanh a = P / (2 - P)` with `P = 1 - exp(-2 a)` and `tanh a = 1 - 2 / (T + 2)` with
`T = exp(2 a) - 1`, and bounds on `exp` at the thresholds of the code.
-/

namespace Library.Numerics.Float64.Tanh.TanhWords
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem abs_value (w : UInt64) : value (Wasm.IEEE64.abs w) = |value w| := by
  obtain ⟨he, hf, hs⟩ := F64Sign.fields_abs w
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.abs w) = Wasm.IEEE64.scaledMagnitude w := by
    simp [Wasm.IEEE64.scaledMagnitude, he, hf]
  rw [Expm1PathsEdge.value_of_sign _ hs, hm, Expm1PathsEdge.abs_value]

theorem abs_finite (w : UInt64) (h : Finite w) : Finite (Wasm.IEEE64.abs w) := by
  obtain ⟨he, -, -⟩ := F64Sign.fields_abs w
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at h ⊢
  rw [he]
  exact h

theorem abs_sign (w : UInt64) : Wasm.IEEE64.sign (Wasm.IEEE64.abs w) = false :=
  (F64Sign.fields_abs w).2.2

/-- The exponent field of a word with value in `[2 ^ -1022, 32)` lies in `[1, 1028)`. -/
theorem exponent_range (a : UInt64) (hlo : 1 / 2 ^ 1022 ≤ |value a|) (hhi : |value a| < 32) :
    1 ≤ Wasm.IEEE64.exponent a ∧ Wasm.IEEE64.exponent a < 1028 := by
  constructor
  · have h := F64Magnitude.exponent_ge_of_value (Wasm.IEEE64.abs a) 1 le_rfl
      (by rw [abs_value]; exact le_of_eq_of_le (by norm_num) hlo)
    rwa [(F64Sign.fields_abs a).1] at h
  · have hb : |value (F64ExponentBounds.boundary 1028)| = 32 := by
      rw [F64ExponentBounds.boundary, F64PositiveSpacing.boundary_value 1028 (by norm_num)
        (by norm_num), abs_of_pos (by positivity)]
      norm_num
    exact F64ExponentBounds.exponent_lt_of_magnitude_lt a 1028 (by norm_num) (by rw [hb]; exact hhi)

/-- Doubling a normal word below 32 is exact. -/
theorem double_value (a : UInt64) (haf : Finite a) (hlo : 1 / 2 ^ 1022 ≤ |value a|)
    (hhi : |value a| < 32) :
    Finite (Wasm.IEEE64.mul Expm1Words.two a) ∧
      value (Wasm.IEEE64.mul Expm1Words.two a) = 2 * value a := by
  obtain ⟨he1, he2⟩ := exponent_range a hlo hhi
  rw [Expm1FormWords.two_eq]
  have h := F64PowerScale.mul_power_finite 1024 a (by norm_num) (by norm_num) haf he1
    (by omega) (by omega)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  norm_num

/-- Multiplying a normal word below 32 by `-2` is exact. -/
theorem neg_double_value (a : UInt64) (haf : Finite a) (hlo : 1 / 2 ^ 1022 ≤ |value a|)
    (hhi : |value a| < 32) :
    Finite (Wasm.IEEE64.mul Expm1Words.negTwo a) ∧
      value (Wasm.IEEE64.mul Expm1Words.negTwo a) = -(2 * value a) := by
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value a haf
  have hne := (F64Sign.fields_negate a).1
  have hn : |value (Wasm.IEEE64.negate a)| = |value a| := by rw [hnv, abs_neg]
  obtain ⟨he1, he2⟩ := exponent_range (Wasm.IEEE64.negate a) (by rw [hn]; exact hlo)
    (by rw [hn]; exact hhi)
  rw [Expm1FormWords.mul_negTwo a haf,
    F64NearestScale.mul_comm_finite _ _ hnf (Expm1FormWords.power_finite 1024 (by norm_num))]
  have h := F64PowerScale.mul_power_finite 1024 (Wasm.IEEE64.negate a) (by norm_num)
    (by norm_num) hnf he1 (by omega) (by omega)
  refine ⟨h.1, ?_⟩
  rw [h.2, hnv]
  norm_num

/-- `tanh a = P / (2 - P)` with `P = 1 - exp(-2 a)`. -/
theorem tanh_small_form (a : ℝ) :
    Real.tanh a = (1 - Real.exp (-(2 * a))) / (2 - (1 - Real.exp (-(2 * a)))) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp (-(2 * a)) = Real.exp (-a) * Real.exp (-a) := by
    rw [← Real.exp_add]; ring_nf
  have ha : Real.exp a = (Real.exp (-a))⁻¹ := by rw [← Real.exp_neg, neg_neg]
  have hq := Real.exp_pos (-a)
  set b := Real.exp (-a)
  have hb : b ≠ 0 := hq.ne'
  have hd1 : b⁻¹ + b ≠ 0 := by positivity
  have hd2 : 2 - (1 - b * b) ≠ 0 := by nlinarith
  rw [h1, ha, div_eq_div_iff hd1 hd2]
  field_simp
  ring

/-- `tanh a = 1 - 2 / (T + 2)` with `T = exp(2 a) - 1`. -/
theorem tanh_large_form (a : ℝ) :
    Real.tanh a = 1 - 2 / ((Real.exp (2 * a) - 1) + 2) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  have hp := Real.exp_pos a
  set b := Real.exp a
  have hb : b ≠ 0 := hp.ne'
  have hd1 : b + b⁻¹ ≠ 0 := by positivity
  have hd2 : b * b - 1 + 2 ≠ 0 := by nlinarith
  rw [h1, Real.exp_neg, eq_sub_iff_add_eq, div_add_div _ _ hd1 hd2, div_eq_one_iff_eq (by
    positivity)]
  field_simp
  ring

/-- `exp` at a point of `[-1, 1]` from the Taylor polynomial of degree 7. -/
theorem exp_taylor (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 +
      x ^ 7 / 5040)| ≤ |x| ^ 8 * (9 / 322560) := by
  have h := TaylorRemainder.exp_remainder x hx 8 (by norm_num)
  rw [Expm1FormBase.expCoeffs_eight] at h
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at h
  norm_num [Nat.factorial] at h
  convert h using 2 <;> ring

theorem exp_bounds :
    Real.exp (-(34657359 / 10 ^ 8)) ≤ 71 / 100 ∧
      35 / 100 ≤ Real.exp (-(10397206 / 10 ^ 7)) ∧
      Real.exp (-(10397205 / 10 ^ 7)) ≤ 36 / 100 ∧
      13 / 100 ≤ Real.exp (-2) ∧
      738 / 100 ≤ Real.exp 2 ∧ Real.exp 1 ≤ 3 := by
  have e1 := exp_taylor (-(34657359 / 10 ^ 8)) (by norm_num [abs_of_neg])
  have e2 := exp_taylor (-(5198603 / 10 ^ 7)) (by norm_num [abs_of_neg])
  have e3 := exp_taylor (-(51986025 / 10 ^ 8)) (by norm_num [abs_of_neg])
  have e4 := exp_taylor (-1) (by norm_num)
  have e5 := exp_taylor 1 (by norm_num)
  have s2 : Real.exp (-(10397206 / 10 ^ 7)) = Real.exp (-(5198603 / 10 ^ 7)) ^ 2 := by
    rw [sq, ← Real.exp_add]; norm_num
  have s3 : Real.exp (-(10397205 / 10 ^ 7)) = Real.exp (-(51986025 / 10 ^ 8)) ^ 2 := by
    rw [sq, ← Real.exp_add]; norm_num
  have s4 : Real.exp (-2) = Real.exp (-1) ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
  have s5 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
  rw [abs_le] at e1 e2 e3 e4 e5
  norm_num at e1 e2 e3 e4 e5
  obtain ⟨a1, b1⟩ := e1
  obtain ⟨a2, b2⟩ := e2
  obtain ⟨a3, b3⟩ := e3
  obtain ⟨a4, b4⟩ := e4
  obtain ⟨a5, b5⟩ := e5
  refine ⟨by linarith, ?_, ?_, ?_, ?_, by linarith⟩
  · rw [s2]; nlinarith
  · rw [s3]; nlinarith [Real.exp_pos (-(51986025 / 10 ^ 8))]
  · rw [s4]; nlinarith
  · rw [s5]; nlinarith

#print axioms double_value
#print axioms neg_double_value
#print axioms tanh_small_form
#print axioms tanh_large_form
#print axioms exp_bounds

end Library.Numerics.Float64.Tanh.TanhWords
