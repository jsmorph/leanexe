import Project.GeluWide.Argument
import Project.ExpNeg.Numerical
import Project.ExpWide.Reduction
import Project.Softmax.Order

namespace Project.GeluWide
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem exponential_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 8) :
    let e := ExpNeg.evaluate (F64Order.negativeAbsBits (Gelu.argumentMagnitude a))
    Approximation e (Real.exp (-Gelu.Real.argument (value a))) 2 (5000*arithmeticEpsilon) := by
  have hz := negative_argument_error a hf ha hu
  have he := ExpNeg.evaluate_relative_error _ hz.1 (by linarith [hz.2.1]) hz.2.2.1
  have hb := argument_bounds (value a) ha hu
  have hp := ExpWide.perturbed_exp (-Gelu.Real.argument (value a)) _ (440*arithmeticEpsilon)
    (by linarith [hb.1]) hz.2.2.2 (by norm_num [arithmeticEpsilon])
  have he1 : Real.exp (value (F64Order.negativeAbsBits (Gelu.argumentMagnitude a))) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hz.2.2.1
  have hround : |value (ExpNeg.evaluate (F64Order.negativeAbsBits (Gelu.argumentMagnitude a))) -
      Real.exp (value (F64Order.negativeAbsBits (Gelu.argumentMagnitude a)))| ≤
        4029*arithmeticEpsilon :=
    he.2.2.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he1
        (by norm_num [arithmeticEpsilon] : 0 ≤ 4029*arithmeticEpsilon))
  refine ⟨he.1, ?_, ?_⟩
  · rw [abs_of_pos he.2.1]
    have hh := (abs_le.mp hround).2
    norm_num [arithmeticEpsilon] at hh ⊢
    linarith
  · exact (abs_sub_le _ _ _).trans ((add_le_add hround hp).trans
      (by norm_num [arithmeticEpsilon]))

theorem denominator_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 8) :
    let d := Wasm.IEEE64.add 0x3FF0000000000000
      (ExpNeg.evaluate (F64Order.negativeAbsBits (Gelu.argumentMagnitude a)))
    Approximation d (1+Real.exp (-Gelu.Real.argument (value a))) 4 (5003*arithmeticEpsilon) ∧
      1/2 ≤ value d := by
  have he := exponential_error a hf ha hu
  have hd := (Gelu.one_approximation.add he (bound := 3) (by norm_num) (by norm_num)
    (by norm_num)).weaken (b' := 4) (e' := 5003*arithmeticEpsilon)
      (by norm_num [arithmeticEpsilon]) (by ring_nf; rfl)
  refine ⟨hd, ?_⟩
  have hh := (abs_le.mp hd.accuracy).1
  have hp := Real.exp_pos (-Gelu.Real.argument (value a))
  norm_num [arithmeticEpsilon] at hh ⊢
  linarith

theorem gelu_negative_logistic (a : ℝ) :
    Gelu.Real.gelu (-a) = (-a*Real.exp (-Gelu.Real.argument a))/(1+Real.exp (-Gelu.Real.argument a)) := by
  rw [Gelu.Real.gelu_neg, Gelu.Real.gelu_logistic]
  have hd : 1+Real.exp (-Gelu.Real.argument a) ≠ 0 := by positivity
  field_simp
  ring

theorem evaluate_error (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 8) :
    Finite (evaluate x) ∧ |value (evaluate x)-Gelu.Real.gelu (value x)| ≤
      200000*arithmeticEpsilon := by
  let a := F64Order.absBits x
  let e := ExpNeg.evaluate (F64Order.negativeAbsBits (Gelu.argumentMagnitude a))
  let d := Wasm.IEEE64.add 0x3FF0000000000000 e
  let r := 1+Real.exp (-Gelu.Real.argument (value a))
  have haf : Finite a := F64Order.absBits_finite x hf
  have hav : value a = |value x| := F64Order.absBits_value x
  have ha : 0 ≤ value a := by rw [hav]; exact abs_nonneg _
  have hu : value a ≤ 8 := by rw [hav]; exact hx
  have he := exponential_error a haf ha hu
  have hd := denominator_error a haf ha hu
  change Approximation d r 4 (5003*arithmeticEpsilon) ∧ 1/2 ≤ value d at hd
  have hr : 1 ≤ r := by dsimp [r]; linarith [Real.exp_pos (-Gelu.Real.argument (value a))]
  have hmag : |Gelu.Real.gelu (value a)| ≤ 8 :=
    (Gelu.Real.gelu_magnitude _).trans (by rw [abs_of_nonneg ha]; exact hu)
  have hratio : |value a/r| ≤ 8 := by
    simpa only [Gelu.Real.gelu_logistic] using hmag
  unfold evaluate
  by_cases hs : x < 0x8000000000000000
  · rw [ite_eq_left hs]
    have hnum := Approximation.exact a haf 8 (by rw [abs_of_nonneg ha]; exact hu)
    have hq := hnum.div_pos hd.1 (by norm_num : (0:ℝ) < 1/2) hd.2
      (by linarith : 0 < r) hratio (bound := 16) (by norm_num) (by norm_num) (by norm_num)
    have hv : value a = value x := by rw [hav, abs_of_nonneg (Softmax.value_nonnegative hs)]
    refine ⟨hq.finite, ?_⟩
    have herr := hq.accuracy
    change |value (Wasm.IEEE64.div a d)-value a/r| ≤ _ at herr
    rw [← Gelu.Real.gelu_logistic (value a), hv] at herr
    exact herr.trans (by norm_num [arithmeticEpsilon])
  · rw [ite_eq_right hs]
    have hneg : Approximation (F64Order.negativeAbsBits a) (-value a) 8 0 := by
      refine ⟨F64Order.negativeAbsBits_finite a haf, ?_, ?_⟩ <;>
        rw [F64Order.negativeAbsBits_value, abs_of_nonneg ha]
      · simpa only [abs_neg, abs_of_nonneg ha] using hu
      · simp
    have hreal : |Real.exp (-Gelu.Real.argument (value a))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (argument_bounds _ ha hu).1)
    have hnum := (hneg.mul he hreal (bound := 16) (by norm_num) (by norm_num)
      (by norm_num)).weaken (b' := 17) (e' := 40016*arithmeticEpsilon)
        (by norm_num [arithmeticEpsilon]) (by ring_nf; rfl)
    have hnr : |(-value a*Real.exp (-Gelu.Real.argument (value a)))/r| ≤ 8 := by
      rw [← gelu_negative_logistic]
      exact (Gelu.Real.gelu_magnitude _).trans (by rw [abs_neg, abs_of_nonneg ha]; exact hu)
    have hq := hnum.div_pos hd.1 (by norm_num : (0:ℝ) < 1/2) hd.2
      (by linarith : 0 < r) hnr (bound := 34) (by norm_num) (by norm_num) (by norm_num)
    have hv : -value a = value x := by
      rw [hav, abs_of_nonpos (Softmax.value_nonpositive hs), neg_neg]
    refine ⟨hq.finite, ?_⟩
    have herr := hq.accuracy
    change |value (Wasm.IEEE64.div (Wasm.IEEE64.mul (F64Order.negativeAbsBits a) e) d)-
      (-value a*Real.exp (-Gelu.Real.argument (value a)))/r| ≤ _ at herr
    rw [← gelu_negative_logistic, hv] at herr
    exact herr.trans (by norm_num [arithmeticEpsilon])

#print axioms evaluate_error
end Project.GeluWide
