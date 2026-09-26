import Project.Lidar.Summary
import Project.Lidar.Continuous

namespace Project.Lidar.QueryGeometry
open LeanExe.WGSL

def Hit (input : UInt.Input) (hits : Nat → ℝ → Prop) (t : ℝ) : Prop :=
  ∃ i, i < 4 ∧ Summary.requested (input.params 3) i = true ∧ hits i t

theorem selected_first (input : UInt.Input) (hits : Nat → ℝ → Prop)
    (i : Nat) (first : Continuous.FirstHit (hits i) (input.params 2) (input.scene i)) :
    Continuous.FirstHit
      (fun t => Summary.requested (input.params 3) i = true ∧ hits i t)
      (input.params 2) (Summary.distance input i) := by
  cases selected : Summary.requested (input.params 3) i with
  | false => simp [Summary.distance, selected, Continuous.FirstHit]
  | true => simpa [Summary.distance, selected] using first

/-- The GPU summary's nearest selected distance has the geometric first-hit
property whenever each resident beam result has that property. -/
theorem nearest_first (input : UInt.Input) (hits : Nat → ℝ → Prop)
    (first : ∀ i, i < 4 → Continuous.FirstHit (hits i) (input.params 2) (input.scene i)) :
    Continuous.FirstHit (Hit input hits) (input.params 2) (Summary.nearest input) := by
  have h := Continuous.first_min (selected_first input hits 0 (first 0 (by decide)))
    (Continuous.first_min (selected_first input hits 1 (first 1 (by decide)))
      (Continuous.first_min (selected_first input hits 2 (first 2 (by decide)))
        (selected_first input hits 3 (first 3 (by decide)))))
  have same : (fun t =>
      (Summary.requested (input.params 3) 0 = true ∧ hits 0 t) ∨
      (Summary.requested (input.params 3) 1 = true ∧ hits 1 t) ∨
      (Summary.requested (input.params 3) 2 = true ∧ hits 2 t) ∨
      (Summary.requested (input.params 3) 3 = true ∧ hits 3 t)) = Hit input hits := by
    funext t
    apply propext
    constructor
    · intro h
      rcases h with h | h | h | h
      · exact ⟨0,by decide,h⟩
      · exact ⟨1,by decide,h⟩
      · exact ⟨2,by decide,h⟩
      · exact ⟨3,by decide,h⟩
    · rintro ⟨i,hi,selected,hit⟩
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> simp [selected,hit]
  rw [same] at h
  exact h

#print axioms nearest_first
end Project.Lidar.QueryGeometry
