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

end Verified.Examples.FourierSpec
