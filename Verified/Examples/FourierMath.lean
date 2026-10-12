import Verified.Examples.FourierSpec

namespace Verified.Examples.FourierSpec

open CodeLib.IEEE64
open scoped BigOperators

theorem phase_decompose (n m : Nat) (hn : 0 < n) :
    phase n m = phase n (m % n) + ((m / n : Nat) : ℝ) * (2 * Real.pi) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hm : (m : ℝ) = ((m % n : Nat) : ℝ) + (n : ℝ) * ((m / n : Nat) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div m n).symm
  unfold phase
  rw [hm]
  field_simp [hn0]

theorem cos_phase_mod (n m : Nat) (hn : 0 < n) :
    Real.cos (phase n (m % n)) = Real.cos (phase n m) := by
  rw [phase_decompose n m hn, Real.cos_add_nat_mul_two_pi]

theorem sin_phase_mod (n m : Nat) (hn : 0 < n) :
    Real.sin (phase n (m % n)) = Real.sin (phase n m) := by
  rw [phase_decompose n m hn, Real.sin_add_nat_mul_two_pi]

theorem inputNorm_nonneg (xs : Array Float) : 0 ≤ inputNorm xs := by
  unfold inputNorm
  exact Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem realDFT_abs_le_inputNorm (xs : Array Float) (k : Nat) :
    |realDFT xs k| ≤ inputNorm xs := by
  unfold realDFT inputNorm
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  calc
    |value xs[2 * j]!.toBits * Real.cos (phase (xs.size / 2) (j * k)) +
        value xs[2 * j + 1]!.toBits * Real.sin (phase (xs.size / 2) (j * k))| ≤
      |value xs[2 * j]!.toBits * Real.cos (phase (xs.size / 2) (j * k))| +
        |value xs[2 * j + 1]!.toBits * Real.sin (phase (xs.size / 2) (j * k))| :=
      abs_add_le _ _
    _ ≤ |value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits| := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

theorem imagDFT_abs_le_inputNorm (xs : Array Float) (k : Nat) :
    |imagDFT xs k| ≤ inputNorm xs := by
  unfold imagDFT inputNorm
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  calc
    |value xs[2 * j + 1]!.toBits * Real.cos (phase (xs.size / 2) (j * k)) -
        value xs[2 * j]!.toBits * Real.sin (phase (xs.size / 2) (j * k))| ≤
      |value xs[2 * j + 1]!.toBits * Real.cos (phase (xs.size / 2) (j * k))| +
        |value xs[2 * j]!.toBits * Real.sin (phase (xs.size / 2) (j * k))| :=
      abs_sub _ _
    _ ≤ |value xs[2 * j]!.toBits| + |value xs[2 * j + 1]!.toBits| := by
      simp only [abs_mul]
      have hc := mul_le_of_le_one_right (abs_nonneg (value xs[2 * j + 1]!.toBits))
        (Real.abs_cos_le_one (phase (xs.size / 2) (j * k)))
      have hs := mul_le_of_le_one_right (abs_nonneg (value xs[2 * j]!.toBits))
        (Real.abs_sin_le_one (phase (xs.size / 2) (j * k)))
      linarith

theorem growth_ge_one (n : Nat) : 1 ≤ growth n := by
  unfold growth
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hpow : 1 ≤ (1 + unitRoundoff64) ^ (n + 2) :=
    one_le_pow₀ (by linarith)
  nlinarith

theorem underflow_nonneg (n : Nat) : 0 ≤ underflow n := by
  unfold underflow multiplicationUnderflowEpsilon unitRoundoff64
  positivity

theorem errorBound_nonneg (xs : Array Float) : 0 ≤ errorBound xs := by
  unfold errorBound
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr (growth_ge_one _)) (inputNorm_nonneg xs))
    (underflow_nonneg _)

theorem magnitudeBound_eq_inputNorm_add_errorBound (xs : Array Float) :
    magnitudeBound xs = inputNorm xs + errorBound xs := by
  unfold magnitudeBound errorBound
  ring

theorem realDFT_mod (xs : Array Float) (k : Nat) (hn : 0 < xs.size / 2) :
    realDFT xs k = ∑ j ∈ Finset.range (xs.size / 2),
      (value xs[2 * j]!.toBits * Real.cos (phase (xs.size / 2) (j * k % (xs.size / 2))) +
        value xs[2 * j + 1]!.toBits * Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))) := by
  unfold realDFT
  apply Finset.sum_congr rfl
  intro j _
  rw [cos_phase_mod _ _ hn, sin_phase_mod _ _ hn]

theorem imagDFT_mod (xs : Array Float) (k : Nat) (hn : 0 < xs.size / 2) :
    imagDFT xs k = ∑ j ∈ Finset.range (xs.size / 2),
      (value xs[2 * j + 1]!.toBits * Real.cos (phase (xs.size / 2) (j * k % (xs.size / 2))) -
        value xs[2 * j]!.toBits * Real.sin (phase (xs.size / 2) (j * k % (xs.size / 2)))) := by
  unfold imagDFT
  apply Finset.sum_congr rfl
  intro j _
  rw [cos_phase_mod _ _ hn, sin_phase_mod _ _ hn]

#print axioms phase_decompose
#print axioms cos_phase_mod
#print axioms sin_phase_mod
#print axioms inputNorm_nonneg
#print axioms realDFT_mod
#print axioms imagDFT_mod
#print axioms realDFT_abs_le_inputNorm
#print axioms imagDFT_abs_le_inputNorm
#print axioms errorBound_nonneg
#print axioms magnitudeBound_eq_inputNorm_add_errorBound

end Verified.Examples.FourierSpec
