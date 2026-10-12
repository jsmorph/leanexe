import Verified.Examples.FourierInverseLoop
import Verified.Examples.FourierInverseBounds

namespace Verified.Examples.FourierInverse

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx

noncomputable def realReference (xs : Array Float) (k : Nat) : ℝ :=
  FourierPositive.realReference xs k / (xs.size / 2 : ℕ)

noncomputable def imagReference (xs : Array Float) (k : Nat) : ℝ :=
  FourierPositive.imagReference xs k / (xs.size / 2 : ℕ)

noncomputable def errorBound (xs : Array Float) : ℝ :=
  (FourierSpec.errorBound xs + unitRoundoff64 * FourierSpec.magnitudeBound xs) /
    (xs.size / 2 : ℕ) + multiplicationUnderflowEpsilon

def Accuracy (xs : Array Float) : Prop :=
  (Fourier.inverse xs).size = 2 * (xs.size / 2) ∧
    ∀ k, k < xs.size / 2 →
      Finite (Fourier.inverse xs)[2 * k]!.toBits ∧
      Finite (Fourier.inverse xs)[2 * k + 1]!.toBits ∧
      |value (Fourier.inverse xs)[2 * k]!.toBits - realReference xs k| ≤ errorBound xs ∧
      |value (Fourier.inverse xs)[2 * k + 1]!.toBits - imagReference xs k| ≤ errorBound xs

theorem inverse_accuracy (xs : Array Float) (h : FourierSpec.Admissible xs) : Accuracy xs := by
  refine ⟨FourierInverseLoop.inverse_size xs h.1, ?_⟩
  intro k hk
  have hn : 0 < xs.size / 2 := by omega
  obtain ⟨hr, hi⟩ := (FourierPositive.accuracy xs h).2 k hk
  have hrn := FourierInverseBounds.normalize_near xs h hn _ _ hr
    (FourierPositive.realReference_abs xs k)
  have hin := FourierInverseBounds.normalize_near xs h hn _ _ hi
    (FourierPositive.imagReference_abs xs k)
  rw [FourierInverseLoop.inverse_get_real xs h.1 k hk,
    FourierInverseLoop.inverse_get_imag xs h.1 k hk]
  exact ⟨hrn.1, hin.1, hrn.2, hin.2⟩

#print axioms inverse_accuracy

end Verified.Examples.FourierInverse
