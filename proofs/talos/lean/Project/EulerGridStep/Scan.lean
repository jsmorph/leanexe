import Project.EulerGridStep.Model
import Project.EulerConservative.Outputs

namespace Project.EulerGridStep.Scan
open Project.EulerConservative.Model (positiveBits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def stateAt (input : Array UInt64) (index : Nat) : Project.EulerConservative.Model.CheckedSideBits :=
  Project.EulerConservative.Model.sideCheckedBits (input.getD (3 * index) 0)
    (input.getD (3 * index + 1) 0) (input.getD (3 * index + 2) 0)

theorem scan_succ (input : Array UInt64) (index : Nat) (speed : UInt64) (fuel : Nat) :
    Model.scan input index speed (fuel + 1) =
      if (stateAt input index).status == 0 then
        Model.scan input (index + 1)
          (if speed ≤ (stateAt input index).speed then (stateAt input index).speed else speed) fuel
      else ⟨1, 0⟩ := rfl

theorem state_speed_positive (input : Array UInt64) (index : Nat)
    (h : (stateAt input index).status = 0) : positiveBits (stateAt input index).speed = true :=
  (Project.EulerConservative.Safety.accepted_outputPositive _ _ _ h).2

theorem scan_bounds (input : Array UInt64) (index : Nat) (speed : UInt64) (fuel : Nat)
    (h : (Model.scan input index speed fuel).status = 0) :
    speed ≤ (Model.scan input index speed fuel).speed ∧
    ∀ offset < fuel, (stateAt input (index + offset)).status = 0 ∧
      (stateAt input (index + offset)).speed ≤ (Model.scan input index speed fuel).speed := by
  induction fuel generalizing index speed with
  | zero => simp [Model.scan]
  | succ fuel ih =>
    rw [scan_succ] at h ⊢
    cases hs : (stateAt input index).status == 0 with
    | false => simp only [hs, Bool.false_eq_true, ite_false] at h; contradiction
    | true =>
      simp only [hs, ite_true] at h ⊢
      let next := if speed ≤ (stateAt input index).speed then (stateAt input index).speed else speed
      have hb := ih (index := index + 1) (speed := next) h
      have hseed : speed ≤ next := by
        dsimp only [next]
        split
        · assumption
        · exact UInt64.le_refl _
      have hstate : (stateAt input index).speed ≤ next := by
        dsimp only [next]
        split
        · exact UInt64.le_refl _
        · rename_i hnot
          apply UInt64.le_iff_toNat_le.mpr
          simp only [UInt64.le_iff_toNat_le] at hnot
          omega
      refine ⟨UInt64.le_trans hseed hb.1, ?_⟩
      intro offset ho
      cases offset with
      | zero => simpa only [Nat.add_zero] using And.intro (beq_iff_eq.mp hs) (UInt64.le_trans hstate hb.1)
      | succ offset =>
        have rest := hb.2 offset (by omega)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

theorem scan_positive_or_zero (input : Array UInt64) (index : Nat) (speed : UInt64) (fuel : Nat)
    (hseed : speed = 0 ∨ positiveBits speed = true)
    (h : (Model.scan input index speed fuel).status = 0) :
    (Model.scan input index speed fuel).speed = 0 ∨
      positiveBits (Model.scan input index speed fuel).speed = true := by
  induction fuel generalizing index speed with
  | zero => exact hseed
  | succ fuel ih =>
    rw [scan_succ] at h ⊢
    cases hs : (stateAt input index).status == 0 with
    | false => simp only [hs, Bool.false_eq_true, ite_false] at h; contradiction
    | true =>
      simp only [hs, ite_true] at h ⊢
      apply ih (index := index + 1) (h := h)
      split
      · exact Or.inr (state_speed_positive input index (beq_iff_eq.mp hs))
      · exact hseed

/-- Accepted nonempty scans return a positive finite upper bound on every
checked computed speed. This does not assert an exact-real sound-speed bound. -/
theorem maxSpeed_safe (input : Array UInt64)
    (h : (Model.maxSpeedCheckedBits input).status = 0) :
    positiveBits (Model.maxSpeedCheckedBits input).speed = true ∧
    ∀ index < input.size / 3, (stateAt input index).status = 0 ∧
      CodeLib.IEEE64.value (stateAt input index).speed ≤
        CodeLib.IEEE64.value (Model.maxSpeedCheckedBits input).speed := by
  unfold Model.maxSpeedCheckedBits at h ⊢
  split at h
  · contradiction
  · rename_i hshape
    simp only [hshape, Bool.false_eq_true, ite_false]
    have hn : 0 < input.size / 3 := by
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hshape
      omega
    have hb := scan_bounds input 0 0 (input.size / 3) h
    have hz := scan_positive_or_zero input 0 0 (input.size / 3) (Or.inl rfl) h
    have hp0 := state_speed_positive input 0 (by simpa using (hb.2 0 hn).1)
    have hpositive : positiveBits (Model.scan input 0 0 (input.size / 3)).speed = true := by
      rcases hz with hz | hz
      · have hle := (hb.2 0 hn).2
        simp only [Nat.zero_add, hz] at hle
        have hzero : (stateAt input 0).speed = 0 := by
          apply UInt64.toNat_inj.mp
          simp only [UInt64.le_iff_toNat_le] at hle
          exact Nat.eq_zero_of_le_zero hle
        rw [hzero] at hp0
        contradiction
      · exact hz
    refine ⟨hpositive, ?_⟩
    intro index hi
    obtain ⟨hstate, hle⟩ := hb.2 index hi
    simp only [Nat.zero_add] at hstate hle
    have hp := state_speed_positive input index hstate
    have horder := Project.ProofKit.F64Order.abs_value_mono _ _ (show
        Project.ProofKit.F64Order.absBits (stateAt input index).speed ≤
        Project.ProofKit.F64Order.absBits (Model.scan input 0 0 (input.size / 3)).speed by
      rw [Project.ProofKit.F64Order.absBits_of_positive _ hp,
        Project.ProofKit.F64Order.absBits_of_positive _ hpositive]
      exact hle)
    rw [abs_of_pos (Project.ProofKit.F64Order.positiveBits_spec _ hp).2,
      abs_of_pos (Project.ProofKit.F64Order.positiveBits_spec _ hpositive).2] at horder
    exact ⟨hstate, horder⟩

#print axioms scan_bounds
#print axioms maxSpeed_safe
end Project.EulerGridStep.Scan
