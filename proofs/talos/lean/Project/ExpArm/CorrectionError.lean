import Project.ExpArm.PolynomialRounding
import Project.ExpArm.TableBounds
import Project.ProofKit.RealExponential

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

theorem correction_error (r tail : UInt64) (ideal : ℝ)
    (hf : Finite r) (ht : Finite tail) (hr : |value r| ≤ 3/1000)
    (hb : |value tail| ≤ 1/(2 : ℝ)^53) (hi : |ideal| ≤ 3/1000)
    (he : |value r-ideal| ≤ 1/1000000000000000000) :
    Finite (correctionWord r tail) ∧
    |value (correctionWord r tail) - (value tail + Real.exp ideal - 1)| ≤
      1/100000000000000000 ∧
    |value (correctionWord r tail)| ≤ 4/1000 := by
  have hc := correction_rounding r tail hf ht hr hb
  have hp := idealPolynomial_error (value r) hr
  have hib : Real.exp ideal ≤ 2 := by
    have h := Real.abs_exp_sub_one_le (hi.trans (by norm_num))
    have h' := (abs_le.mp h).2
    linarith
  have hpert := RealExponential.relative_perturbation ideal (value r)
    (1/1000000000000000000) he (by norm_num)
  have hd : |Real.exp (value r)-Real.exp ideal| ≤ 4/1000000000000000000 := by
    exact hpert.trans ((mul_le_mul_of_nonneg_left hib (by norm_num)).trans_eq (by norm_num))
  refine ⟨hc.finite, ?_, hc.magnitude⟩
  have hid : value (correctionWord r tail) - (value tail + Real.exp ideal - 1) =
      (value (correctionWord r tail) - (value tail + idealPolynomial (value r) - 1)) +
      (idealPolynomial (value r)-Real.exp (value r)) +
      (Real.exp (value r)-Real.exp ideal) := by ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hc.accuracy hp.le) hd).trans (by norm_num))

set_option maxRecDepth 4096 in
theorem table_finite : ∀ i : Fin 128,
    Finite (tableScaleWord i) ∧ Finite table[2*i.val]! := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem table_real_bounds (i : Nat) (hi : i < 128) :
    Finite (tableScaleWord i) ∧ Finite table[2*i]! ∧
    1 ≤ value (tableScaleWord i) ∧ value (tableScaleWord i) < 2 ∧
    |value table[2*i]!| ≤ 1/(2 : ℝ)^53 := by
  have hf := table_finite ⟨i, hi⟩
  have h := table_rational_bounds ⟨i, hi⟩
  refine ⟨hf.1, hf.2, ?_, ?_, ?_⟩
  · have hc := (Rat.cast_le (K := ℝ)).mpr h.1
    simpa only [Rat.cast_one, F64Rational.decode_cast] using hc
  · have hc := (Rat.cast_lt (K := ℝ)).mpr h.2.1
    simpa only [Rat.cast_ofNat, F64Rational.decode_cast] using hc
  · have hc : ((|F64Rational.decode table[2*i]!| : ℚ) : ℝ) ≤
        ((1/(2 : ℚ)^53 : ℚ) : ℝ) := Rat.cast_le.mpr h.2.2.1
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
      F64Rational.decode_cast] using hc

theorem table_correction_error (r : UInt64) (ideal : ℝ) (i : Nat) (hi : i < 128)
    (hf : Finite r) (hr : |value r| ≤ 3/1000) (hideal : |ideal| ≤ 3/1000)
    (he : |value r-ideal| ≤ 1/1000000000000000000) :
    |value (tableScaleWord i) * (1 + value (correctionWord r table[2*i]!)) -
      Real.exp ((i : ℝ)*Real.log 2/128 + ideal)| ≤ 3/100000000000000000 := by
  let h := value (tableScaleWord i)
  let t := value table[2*i]!
  let c := value (correctionWord r table[2*i]!)
  have hb := table_real_bounds i hi
  have hc := correction_error r table[2*i]! ideal hf hb.2.1 hr hb.2.2.2.2 hideal he
  have hs := table_error i hi
  have hsmall : |Real.exp ideal-1| ≤ 6/1000 :=
    (Real.abs_exp_sub_one_le (hideal.trans (by norm_num))).trans (by linarith)
  have hexp : |Real.exp ideal| ≤ 2 := by
    rw [abs_of_pos (Real.exp_pos _)]
    have ht := (abs_le.mp hsmall).2
    linarith
  have htail : |t*(1-Real.exp ideal)| ≤ (1/(2 : ℝ)^53)*(6/1000) := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hb.2.2.2.2 hsmall (abs_nonneg _) (by positivity)
  have hlocal : |(1+c)-(1+t)*Real.exp ideal| ≤
      1/100000000000000000 + (1/(2 : ℝ)^53)*(6/1000) := by
    rw [show (1+c)-(1+t)*Real.exp ideal =
      (c-(t+Real.exp ideal-1)) + t*(1-Real.exp ideal) by ring]
    exact (abs_add_le _ _).trans (add_le_add hc.2.1 htail)
  have hh : |h| ≤ 2 := by
    rw [abs_of_pos (by dsimp [h]; linarith [hb.2.2.1])]
    exact hb.2.2.2.1.le
  have h1 := mul_le_mul hh hlocal (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul hs hexp (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1/(2 : ℝ)^104)
  have hid : h*(1+c) - Real.exp ((i : ℝ)*Real.log 2/128 + ideal) =
      h*((1+c)-(1+t)*Real.exp ideal) +
      (h*(1+t)-Real.exp ((i : ℝ)*Real.log 2/128))*Real.exp ideal := by
    rw [Real.exp_add]
    ring
  change |h*(1+c)-Real.exp ((i : ℝ)*Real.log 2/128 + ideal)| ≤ _
  rw [hid]
  have ht := abs_add_le (h*((1+c)-(1+t)*Real.exp ideal))
    ((h*(1+t)-Real.exp ((i : ℝ)*Real.log 2/128))*Real.exp ideal)
  simp only [abs_mul] at ht
  exact ht.trans ((add_le_add h1 h2).trans (by norm_num))

#print axioms table_correction_error
end Project.ExpArm
