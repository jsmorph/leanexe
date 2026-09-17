import Project.ProofKit.F32MulBounds

namespace Project.ProofKit.F32DyadicReal
open CodeLib.IEEE32

/-- Interpret the pure rounder's exact dyadic input as a real value. -/
noncomputable def exactValue (negative : Bool) (n frac : Nat) : ℝ :=
  (if negative then -(n:ℝ) else n) / 2^(frac+149)

theorem exact_abs (negative : Bool) (n frac : Nat) :
    |exactValue negative n frac| = (n:ℝ) / 2^(frac+149) := by
  cases negative <;> simp [exactValue, abs_div]

theorem real_adaptive (negative : Bool) (n frac : Nat) (hf : 0 < frac)
    (hmax : n < 2^(frac+276)) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n frac) ∧
    |value (Wasm.IEEE32.roundDyadicMagnitude negative n frac) - exactValue negative n frac| ≤
      F32AddBounds.unitRoundoff * max |exactValue negative n frac| F32MulBounds.minNormal := by
  have hs := F32DyadicBounds.dyadic_relative negative n frac hf hmax
  let result := Wasm.IEEE32.roundDyadicMagnitude negative n frac
  let z : Int := (Wasm.IEEE32.scaledMagnitude result : Int) * 2^frac - (n:Int)
  have hz : |(z:ℝ)| * (2:ℝ)^24 ≤ (max n (2^(frac+23)) : Nat) := by
    have hi : |z| * (2:Int)^24 ≤ (max n (2^(frac+23)) : Nat) := by
      simpa only [z, result, Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat] using hs.2.2
    exact_mod_cast hi
  have heq : |value result - exactValue negative n frac| = |(z:ℝ)| / 2^(frac+149) := by
    have hsign : Wasm.IEEE32.sign result = negative := hs.2.1
    simp only [value, Wasm.IEEE32.scaledValue, hsign, exactValue]
    have hp : (2:ℝ)^(frac+149) = 2^frac * 2^149 := pow_add _ _ _
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      Int.cast_neg, Int.cast_natCast]
    · have hv : (Wasm.IEEE32.scaledMagnitude result : ℝ) / 2^149 - (n:ℝ)/2^(frac+149) =
          (z:ℝ) / 2^(frac+149) := by
        simp only [z, Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
        rw [hp]
        field_simp
        <;> ring
      rw [hv, abs_div, abs_of_pos (show (0:ℝ) < 2^(frac+149) by positivity)]
    · have hv : -(Wasm.IEEE32.scaledMagnitude result : ℝ) / 2^149 - -(n:ℝ)/2^(frac+149) =
          -(z:ℝ) / 2^(frac+149) := by
        simp only [z, Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
        rw [hp]
        field_simp
        <;> ring
      rw [hv, abs_div, abs_neg, abs_of_pos (show (0:ℝ) < 2^(frac+149) by positivity)]
  refine ⟨hs.1, ?_⟩
  change |value result - exactValue negative n frac| ≤ _
  rw [heq, exact_abs]
  calc
    |(z:ℝ)| / 2^(frac+149) =
        (|(z:ℝ)| * 2^24) / ((2:ℝ)^24 * 2^(frac+149)) := by field_simp
    _ ≤ ((max n (2^(frac+23)) : Nat):ℝ) / ((2:ℝ)^24 * 2^(frac+149)) :=
      div_le_div_of_nonneg_right hz (by positivity)
    _ = F32AddBounds.unitRoundoff * max ((n:ℝ)/2^(frac+149)) F32MulBounds.minNormal := by
      have hm : F32MulBounds.minNormal = (2:ℝ)^(frac+23) / 2^(frac+149) := by
        rw [pow_add, pow_add]
        simp [F32MulBounds.minNormal]
        field_simp
        <;> ring
      rw [hm, max_div_div_right (show 0 ≤ (2:ℝ)^(frac+149) by positivity)]
      simp only [Nat.cast_max, Nat.cast_pow, Nat.cast_ofNat, F32AddBounds.unitRoundoff]
      ring

theorem real_mixed (negative : Bool) (n frac : Nat) (hf : 0 < frac)
    (hmax : n < 2^(frac+276)) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n frac) ∧
    |value (Wasm.IEEE32.roundDyadicMagnitude negative n frac) - exactValue negative n frac| ≤
      F32AddBounds.unitRoundoff * |exactValue negative n frac| + F32MulBounds.multiplicationUnderflowEpsilon := by
  have hs := real_adaptive negative n frac hf hmax
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hu : 0 ≤ F32AddBounds.unitRoundoff := by norm_num [F32AddBounds.unitRoundoff]
  have hm : 0 ≤ F32MulBounds.minNormal := by norm_num [F32MulBounds.minNormal]
  calc
    _ ≤ F32AddBounds.unitRoundoff * (|exactValue negative n frac| + F32MulBounds.minNormal) :=
      mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith [abs_nonneg (exactValue negative n frac)])) hu
    _ = _ := by rw [mul_add]; congr 1; norm_num [F32AddBounds.unitRoundoff,
      F32MulBounds.minNormal, F32MulBounds.multiplicationUnderflowEpsilon]

#print axioms real_adaptive
#print axioms real_mixed
end Project.ProofKit.F32DyadicReal
