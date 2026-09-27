import Project.GeluWide.Model
import Project.Gelu.Argument

namespace Project.GeluWide
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem coefficient_approximation :
    Approximation 0x3FA6E4E26D4801F7 Gelu.Real.coefficient (1/20) (arithmeticEpsilon/100) := by
  refine ⟨Gelu.coefficient_approximation.finite, Gelu.coefficient_approximation.magnitude, ?_⟩
  norm_num [Gelu.Real.coefficient, value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]

theorem scale_approximation :
    Approximation 0x3FF9884533D43651 (2*Gelu.Real.scale) 2 arithmeticEpsilon := by
  have hs := Gelu.Real.scale_bounds_precise
  refine ⟨Gelu.scale_approximation.finite, Gelu.scale_approximation.magnitude, ?_⟩
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat, arithmeticEpsilon]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem argument_bounds (a : ℝ) (ha : 0 ≤ a) (hu : a ≤ 8) :
    0 ≤ Gelu.Real.argument a ∧ Gelu.Real.argument a ≤ 50 := by
  have hs : 0 ≤ Gelu.Real.scale ∧ Gelu.Real.scale ≤ 4/5 := by
    have hh := Gelu.Real.scale_bounds
    constructor <;> linarith
  have hc : 0 ≤ Gelu.Real.coefficient ∧ Gelu.Real.coefficient ≤ 9/200 := by
    norm_num [Gelu.Real.coefficient]
  have ha3 : 0 ≤ a^3 := pow_nonneg ha _
  have ha3u : a^3 ≤ 512 := (pow_le_pow_left₀ ha hu 3).trans (by norm_num)
  have hca := mul_le_mul hc.2 ha3u ha3 (by norm_num : (0:ℝ) ≤ 9/200)
  unfold Gelu.Real.argument
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) hs.1) (add_nonneg ha (mul_nonneg hc.1 ha3)), ?_⟩
  have hp := mul_le_mul_of_nonneg_left (show a+Gelu.Real.coefficient*a^3 ≤ 8+9/200*512 by
    linarith) hs.1
  nlinarith only [hp, hs.2]

theorem argumentMagnitude_error (a : UInt64) (hf : Finite a) (ha : |value a| ≤ 8) :
    Approximation (Gelu.argumentMagnitude a) (Gelu.Real.argument (value a)) 115 (440*arithmeticEpsilon) := by
  have h := Approximation.exact a hf 8 ha
  have h1 : Approximation (Wasm.IEEE64.mul a a) (value a*value a) 65 (65*arithmeticEpsilon) :=
    (h.mul h ha (bound := 64) (by norm_num) (by norm_num) (by norm_num)).weaken
      (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hc : |Gelu.Real.coefficient| ≤ 1/20 := by norm_num [Gelu.Real.coefficient]
  have h2 := (h1.mul coefficient_approximation hc (bound := 4)
    (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 5) (e' := 8*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have h3 := (h2.add Gelu.one_approximation (bound := 6)
    (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 7) (e' := 14*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have h4 := (h3.mul h ha (bound := 56)
    (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 57) (e' := 168*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  have hk : |2*Gelu.Real.scale| ≤ 8/5 := by
    have hh := Gelu.Real.scale_bounds
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h5 := (h4.mul scale_approximation hk (bound := 114)
    (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 115) (e' := 440*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  convert h5 using 1 <;> first | rfl | (unfold Gelu.Real.argument; ring)

theorem negative_argument_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 8) :
    let z := F64Order.negativeAbsBits (Gelu.argumentMagnitude a)
    Finite z ∧ -51 ≤ value z ∧ value z ≤ 0 ∧
      |value z - -Gelu.Real.argument (value a)| ≤ 440*arithmeticEpsilon := by
  have h := argumentMagnitude_error a hf (by rw [abs_of_nonneg ha]; exact hu)
  have hb := argument_bounds (value a) ha hu
  have he : |abs (value (Gelu.argumentMagnitude a))-Gelu.Real.argument (value a)| ≤ 440*arithmeticEpsilon := by
    simpa only [abs_of_nonneg hb.1] using (abs_abs_sub_abs_le _ _).trans h.accuracy
  dsimp
  refine ⟨F64Order.negativeAbsBits_finite _ h.finite, ?_, ?_, ?_⟩
  · rw [F64Order.negativeAbsBits_value]
    have hh := (abs_le.mp he).2
    have hu : 440*arithmeticEpsilon ≤ 1 := by norm_num [arithmeticEpsilon]
    linarith
  · rw [F64Order.negativeAbsBits_value]
    exact neg_nonpos.mpr (abs_nonneg _)
  · rw [F64Order.negativeAbsBits_value, neg_sub_neg, abs_sub_comm]
    exact he

#print axioms negative_argument_error

end Project.GeluWide
