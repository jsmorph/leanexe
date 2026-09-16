import Project.Gelu.Model
import Project.Gelu.Real
import Project.ProofKit.F64Approximation

namespace Project.Gelu
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem coefficient_approximation :
    Approximation 0x3FA6E4E26D4801F7 Real.coefficient (1/20) (1/10000000000000000) := by
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_, ?_⟩ <;>
    norm_num [Real.coefficient, value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem scale_approximation :
    Approximation 0x3FF9884533D43651 (2*Real.scale) 2 (1/1000000000000000) := by
  have hk := Real.scale_bounds_precise
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_, ?_⟩
  · norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  · norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem one_approximation : Approximation 0x3FF0000000000000 1 1 0 := by
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_, ?_⟩ <;>
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem argumentMagnitude_error (a : UInt64) (hf : Finite a) (ha : |value a| ≤ 3) :
    Approximation (argumentMagnitude a) (Real.argument (value a)) 27 (1/10000000000) := by
  have h := Approximation.exact a hf 3 ha
  have h1 : Approximation (Wasm.IEEE64.mul a a) (value a * value a) 10 (1/1000000000000) :=
    (h.mul h ha (bound := 9) (by norm_num) (by norm_num) (by norm_num)).weaken
      (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hc : |Real.coefficient| ≤ 1/20 := by norm_num [Real.coefficient]
  have h2 : Approximation (Wasm.IEEE64.mul (Wasm.IEEE64.mul a a) 0x3FA6E4E26D4801F7)
      (value a * value a * Real.coefficient) 2 (1/1000000000000) :=
    (h1.mul coefficient_approximation hc (bound := 1) (by norm_num) (by norm_num)
      (by norm_num)).weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have h3 := (h2.add one_approximation (bound := 3) (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 4) (e' := 2/1000000000000) (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have h4 := (h3.mul h ha (bound := 12) (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 13) (e' := 1/100000000000) (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hk : |2*Real.scale| ≤ 8/5 := by
    have hh := Real.scale_bounds
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h5 := (h4.mul scale_approximation hk (bound := 26) (by norm_num) (by norm_num)
    (by norm_num)).weaken (b' := 27) (e' := 1/10000000000)
      (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  convert h5 using 1 <;> first | rfl | (unfold Real.argument; ring)

theorem negative_argument_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 3) :
    let z := F64Order.negativeAbsBits (argumentMagnitude a)
    Finite z ∧ -8 ≤ value z ∧ value z ≤ 0 ∧
      |value z - -Real.argument (value a)| ≤ 1/10000000000 := by
  have h := argumentMagnitude_error a hf (by rw [abs_of_nonneg ha]; exact hu)
  have hb := Real.argument_bounds (value a) ha hu
  have he : |abs (value (argumentMagnitude a)) - Real.argument (value a)| ≤ 1/10000000000 := by
    simpa only [abs_of_nonneg hb.1] using (abs_abs_sub_abs_le _ _).trans h.accuracy
  dsimp
  refine ⟨F64Order.negativeAbsBits_finite _ h.finite, ?_, ?_, ?_⟩
  · rw [F64Order.negativeAbsBits_value]
    have hh := abs_le.mp he
    linarith
  · rw [F64Order.negativeAbsBits_value]
    exact neg_nonpos.mpr (abs_nonneg _)
  · rw [F64Order.negativeAbsBits_value, neg_sub_neg, abs_sub_comm]
    exact he

#print axioms negative_argument_error
end Project.Gelu
