import Project.Gelu.Argument
import Project.ExpWide.Sharp
import Project.Softmax.Order

namespace Project.Gelu
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem exponential_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 3) :
    let e := ExpWide.evaluate (F64Order.negativeAbsBits (argumentMagnitude a))
    Finite e ∧ 1/1000000000 ≤ value e ∧ value e ≤ 2 ∧
      |value e - Real.exp (-Real.argument (value a))| ≤ 1/290000 := by
  have hz := negative_argument_error a hf ha hu
  have he := ExpWide.evaluate_error_sharp _ hz.1 (by linarith [hz.2.1]) hz.2.2.1
  have hb := Real.argument_bounds (value a) ha hu
  have hp := ExpWide.perturbed_exp (-Real.argument (value a)) _ (1/10000000000)
    (by linarith) hz.2.2.2 (by norm_num)
  have herr : |value (ExpWide.evaluate (F64Order.negativeAbsBits (argumentMagnitude a))) -
      Real.exp (-Real.argument (value a))| ≤ 1/290000 :=
    (abs_sub_le _ _ _).trans ((add_le_add he.2.2 hp).trans (by norm_num))
  have hu1 : Real.exp (-Real.argument (value a)) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (by linarith : -Real.argument (value a) ≤ 0)
  exact ⟨he.1, he.2.1, by linarith [(abs_le.mp herr).2], herr⟩

theorem denominator_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 3) :
    let e := ExpWide.evaluate (F64Order.negativeAbsBits (argumentMagnitude a))
    let d := Wasm.IEEE64.add 0x3FF0000000000000 e
    Finite d ∧ 1 ≤ value d ∧
      |value d - (1 + Real.exp (-Real.argument (value a)))| ≤ 1/280000 := by
  have he := exponential_error a hf ha hu
  have hv1 : value 0x3FF0000000000000 = 1 := by
    have h := abs_le.mp one_approximation.accuracy
    linarith
  have hh := F64ArithmeticBounds.add_error _ _ one_approximation.finite he.1
    3 (by norm_num) (by norm_num) (by
      rw [hv1, abs_of_nonneg (by linarith [he.2.1])]
      linarith [he.2.2.1])
  rw [hv1] at hh
  refine ⟨hh.1, ?_, ?_⟩
  · have h := (abs_le.mp hh.2).1
    have heps : 3*arithmeticEpsilon < (1:ℝ)/1000000000 := by norm_num [arithmeticEpsilon]
    linarith [he.2.1]
  · have h1 := abs_le.mp hh.2
    have h2 := abs_le.mp he.2.2.2
    have heps : arithmeticEpsilon*3 + 1/290000 ≤ (1:ℝ)/280000 := by norm_num [arithmeticEpsilon]
    apply abs_le.mpr
    constructor <;> linarith

theorem quotient_error (a d r : ℝ) (ha : |a| ≤ 3) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (he : |d-r| ≤ 1/280000) : |a/d-a/r| ≤ 3/280000 := by
  have dp : 0 < d := by linarith
  have rp : 0 < r := by linarith
  have hid : a/d-a/r = a*(r-d)/(d*r) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos dp rp)]
  apply (div_le_iff₀ (mul_pos dp rp)).mpr
  have hn : |a*(r-d)| ≤ 3*(1/280000) := by
    rw [abs_mul, abs_sub_comm r d]
    exact mul_le_mul ha he (abs_nonneg _) (by norm_num)
  have hdr : 1 ≤ d*r := by nlinarith [mul_nonneg (by linarith : 0 ≤ d-1) (by linarith : 0 ≤ r-1)]
  linarith

theorem positivePart_error (a : UInt64) (hf : Finite a)
    (ha : 0 ≤ value a) (hu : value a ≤ 3) :
    Finite (positivePart a) ∧ |value (positivePart a)| ≤ 4 ∧
      |value (positivePart a) - Real.gelu (value a)| ≤ 1/90000 := by
  let d := Wasm.IEEE64.add 0x3FF0000000000000
    (ExpWide.evaluate (F64Order.negativeAbsBits (argumentMagnitude a)))
  let r := 1 + Real.exp (-Real.argument (value a))
  have hd := denominator_error a hf ha hu
  change Finite d ∧ 1 ≤ value d ∧ |value d-r| ≤ 1/280000 at hd
  have dp : 0 < value d := by linarith [hd.2.1]
  have d0 : Wasm.IEEE64.scaledMagnitude d ≠ 0 := by
    intro h
    simp [value, Wasm.IEEE64.scaledValue, h] at dp
  have hb : |value a/value d| ≤ 3 := by
    rw [abs_of_nonneg (div_nonneg ha dp.le)]
    apply (div_le_iff₀ dp).mpr
    linarith [hd.2.1]
  have hq := F64ArithmeticBounds.div_error a d hf hd.1 d0 3 (by norm_num) (by norm_num) hb
  have hr : 1 ≤ r := by dsimp [r]; linarith [Real.exp_pos (-Real.argument (value a))]
  have he := quotient_error (value a) (value d) r (by rw [abs_of_nonneg ha]; exact hu)
    hd.2.1 hr hd.2.2
  have herr : |value (positivePart a) - Real.gelu (value a)| ≤ 1/90000 := by
    rw [Real.gelu_logistic]
    exact (abs_sub_le _ _ _).trans ((add_le_add hq.2 he).trans (by norm_num [arithmeticEpsilon]))
  refine ⟨hq.1, ?_, herr⟩
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ 3 herr
    ((Real.gelu_magnitude _).trans (by rw [abs_of_nonneg ha]; exact hu))).trans (by norm_num)

theorem evaluate_error (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 3) :
    Finite (evaluate x) ∧ |value (evaluate x) - Real.gelu (value x)| ≤ 1/80000 := by
  have hp := positivePart_error (F64Order.absBits x) (F64Order.absBits_finite x hf)
    (by rw [F64Order.absBits_value]; exact abs_nonneg _)
    (by rw [F64Order.absBits_value]; exact hx)
  unfold evaluate
  by_cases hs : x < 0x8000000000000000
  · rw [ite_eq_left hs]
    rw [F64Order.absBits_value, abs_of_nonneg (Softmax.value_nonnegative hs)] at hp
    exact ⟨hp.1, hp.2.2.trans (by norm_num)⟩
  · rw [ite_eq_right hs]
    have hv : value (F64Order.absBits x) = -value x := by
      rw [F64Order.absBits_value, abs_of_nonpos (Softmax.value_nonpositive hs)]
    have hsub := F64ArithmeticBounds.sub_error _ _ hp.1 (F64Order.absBits_finite x hf)
      7 (by norm_num) (by norm_num)
      ((abs_sub _ _).trans (by rw [F64Order.absBits_value, abs_abs]; linarith [hp.2.1]))
    refine ⟨hsub.1, ?_⟩
    have he : |(value (positivePart (F64Order.absBits x))-value (F64Order.absBits x)) -
        Real.gelu (value x)| ≤ 1/90000 := by
      rw [hv, Real.gelu_neg] at hp
      rw [hv]
      convert hp.2.2 using 1
      congr 1
      ring
    exact (abs_sub_le _ _ _).trans ((add_le_add hsub.2 he).trans (by norm_num [arithmeticEpsilon]))

#print axioms evaluate_error
end Project.Gelu
