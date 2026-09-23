import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Project.ProofKit.FiniteErrorBound

noncomputable def upper (f : Nat → ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => max (upper f n) (f n)

theorem nonnegative (f : Nat → ℝ) (n : Nat) : 0 ≤ upper f n := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem component_le (f : Nat → ℝ) (n i : Nat) (hi : i < n) : f i ≤ upper f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

#print axioms component_le
end Project.ProofKit.FiniteErrorBound
