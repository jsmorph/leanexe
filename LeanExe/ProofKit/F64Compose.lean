import LeanExe.ProofKit.F64TwoSteps

/-!
Composition of step bounds.  A word within one step of the reference of `y₁` lies within two
steps of the reference of `y₂` when `y₁` and `y₂` are positive and closer than one spacing of a
binade whose start lies below both: their nearest words are then at most one step apart
(`F64RoundNearest.steps_of_nearest`).  This composes a library call that is within one step of
its own exact value, at a computed argument, with the error of that argument.
-/

namespace LeanExe.ProofKit.F64Compose
open CodeLib.IEEE64 F64NearestNonnegative

theorem within_two_of_close (y₁ y₂ : ℝ) (c : UInt64) (h : F64SignedRounding.WithinSteps 1 y₁ c)
    (a : ℕ) (ha1 : 1 ≤ a) (ha : a < 2047)
    (h₁ : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y₁) (h₂ : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y₂)
    (hd : |y₁ - y₂| < (2 : ℝ) ^ (a - 1) / 2 ^ 1074)
    (ht₁ : y₁ < F64PositiveRounding.overflowThreshold)
    (ht₂ : y₂ < F64PositiveRounding.overflowThreshold) :
    F64SignedRounding.WithinSteps 2 y₂ c := by
  have hB := F64PositiveSpacing.boundary_value a ha1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by rw [hB]; positivity
  have hy₁ : 0 ≤ y₁ := by linarith
  have hy₂ : 0 ≤ y₂ := by linarith
  obtain ⟨hcn, hcp⟩ := h
  have hr₁ : F64SignedRounding.roundNearestEven y₁ = F64PositiveRounding.roundNearestEven y₁ := by
    simp only [F64SignedRounding.roundNearestEven, if_pos hy₁]
  rw [hr₁] at hcp
  have hw₁ := (F64NearestEven.roundNearestEven_spec y₁).1
  have hw₂ := (F64NearestEven.roundNearestEven_spec y₂).1
  rw [← F64PositiveRounding.reference_finite y₁ ht₁] at hw₁
  rw [← F64PositiveRounding.reference_finite y₂ ht₂] at hw₂
  have hst := F64RoundNearest.steps_of_nearest y₁ y₂ _ _ hw₁ hw₂ a ha h₁ h₂ hd
  have hra := F64RoundNearest.nearest_above y₁ _ hw₁ a ha h₁
  have hp₁ := F64SignedRounding.positive_reference_le y₁
  rw [F64SignedRounding.position_of_lt (F64PositiveRounding.roundNearestEven y₁) (by omega)] at hcp
  have hcp' := abs_le.mp hcp
  have hc63 : c.toNat < 2 ^ 63 := by
    by_contra hge
    push Not at hge
    have hneg : F64SignedRounding.position c = -((c.toNat - 2 ^ 63 : ℕ) : ℤ) := by
      simp only [F64SignedRounding.position, Wasm.IEEE64.sign, decide_eq_true hge,
        ite_true]
    rw [hneg] at hcp'
    omega
  rw [F64SignedRounding.position_of_lt _ hc63] at hcp'
  exact F64SignedRounding.within_of_nonneg 2 y₂ hy₂ c (by omega) (by omega) (by omega)

#print axioms within_two_of_close

end LeanExe.ProofKit.F64Compose
