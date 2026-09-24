import Project.EulerRiemann.FrozenReconstruction
import Project.EulerRiemann.FrozenNumericsSafety
import Project.ProofKit.F64MinmodSpec

namespace Project.EulerRiemann.Frozen.Reconstruction
open Project.Euler2DCellStep.Sweep (State StateSafe)
open Project.Euler2DConservative.Guard
open Project.ProofKit.F64Order (finiteBits_iff)

theorem admissibleState_safe (state : State) (h : admissibleState state = true) :
    StateSafe state := by
  have hb := Numerics.stateGuard_spec _ _ _ _ h
  exact ⟨hb, hb.densityPositive, mul_pos (by norm_num : (0 : ℝ) < 2/5) hb.internalPositive⟩

theorem candidate_accepted (center delta : State) (factor : UInt64)
    (h : (candidate center delta factor).status = 0) :
    candidate center delta factor =
      ⟨0, difference center (scale factor delta), sum center (scale factor delta), factor⟩ ∧
    Project.ProofKit.F64Order.finiteBits factor = true ∧
    finiteState (scale factor delta) = true ∧
    admissibleState (difference center (scale factor delta)) = true ∧
    admissibleState (sum center (scale factor delta)) = true := by
  unfold candidate at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · exact ⟨rfl, by simpa only [Bool.and_eq_true, and_assoc] using hg⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem candidate_guards (center delta : State) (factor : UInt64)
    (h : (candidate center delta factor).status = 0) :
    admissibleState (candidate center delta factor).left = true ∧
    admissibleState (candidate center delta factor).right = true := by
  have hc := candidate_accepted center delta factor h
  rw [hc.1]
  exact hc.2.2.2

theorem limit_status (fuel : Nat) (center delta : State) (factor : UInt64) :
    (limit fuel center delta factor).status = 0 := by
  induction fuel generalizing factor with
  | zero => rfl
  | succ fuel ih =>
      simp only [limit, beq_iff_eq]
      split_ifs with h
      · exact h
      · exact ih _

theorem limit_guards (fuel : Nat) (center delta : State) (factor : UInt64)
    (hcenter : admissibleState center = true) :
    admissibleState (limit fuel center delta factor).left = true ∧
    admissibleState (limit fuel center delta factor).right = true := by
  induction fuel generalizing factor with
  | zero => exact ⟨hcenter, hcenter⟩
  | succ fuel ih =>
      simp only [limit, beq_iff_eq]
      split_ifs with h
      · exact candidate_guards center delta factor h
      · exact ih _

theorem reconstruct_inputs (fuel : Nat) (left center right : State)
    (h : (reconstruct fuel left center right).status = 0) :
    admissibleState left = true ∧ admissibleState center = true ∧
    admissibleState right = true ∧ (slope left center right).status = 0 ∧
    reconstruct fuel left center right =
      limit fuel center (slope left center right).state 0x3FE0000000000000 := by
  unfold reconstruct at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg hs
  · simp only [Bool.and_eq_true] at hg
    exact ⟨hg.1.1, hg.1.2, hg.2, by simpa using hs, rfl⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem reconstruct_safe (fuel : Nat) (left center right : State)
    (h : (reconstruct fuel left center right).status = 0) :
    StateSafe (reconstruct fuel left center right).left ∧
    StateSafe (reconstruct fuel left center right).right := by
  have hi := reconstruct_inputs fuel left center right h
  rw [hi.2.2.2.2]
  have hg := limit_guards fuel center (slope left center right).state
    0x3FE0000000000000 hi.2.1
  exact ⟨admissibleState_safe _ hg.1, admissibleState_safe _ hg.2⟩

theorem reconstruct_behavior (fuel : Nat) (left center right : State) :
    reconstruct fuel left center right = rejectedFaces ∨
      (reconstruct fuel left center right).status = 0 ∧
      StateSafe (reconstruct fuel left center right).left ∧
      StateSafe (reconstruct fuel left center right).right := by
  have hr : reconstruct fuel left center right = rejectedFaces ∨
      (reconstruct fuel left center right).status = 0 := by
    unfold reconstruct
    dsimp only
    split_ifs
    · exact Or.inr (limit_status _ _ _ _)
    · exact Or.inl rfl
    · exact Or.inl rfl
  exact hr.imp_right (fun h => ⟨h, reconstruct_safe fuel left center right h⟩)

theorem reconstruct_unrestricted (fuel : Nat) (left center right : State)
    (hl : admissibleState left = true) (hc : admissibleState center = true)
    (hr : admissibleState right = true) (hs : (slope left center right).status = 0)
    (hf : (candidate center (slope left center right).state 0x3FE0000000000000).status = 0) :
    reconstruct (fuel+1) left center right =
      candidate center (slope left center right).state 0x3FE0000000000000 := by
  simp only [reconstruct, hl, hc, hr, Bool.and_self, ite_true, hs,
    beq_self_eq_true, limit, hf]

#print axioms limit_guards
#print axioms reconstruct_safe
#print axioms reconstruct_behavior
#print axioms reconstruct_unrestricted

end Project.EulerRiemann.Frozen.Reconstruction
