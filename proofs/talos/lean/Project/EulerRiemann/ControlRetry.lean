import Project.EulerRiemann.Control
import Project.EulerRiemann.TraversalModel
import Project.EulerRiemann.TimeBounds

namespace Project.EulerRiemann.Control
open Traversal

theorem retry_status (fuel n : Nat) (time dt : UInt64) (grid : Array Cell) :
    (retry fuel n time dt grid).status = 0 ∨
      (retry fuel n time dt grid).status = 3 ∨
      (retry fuel n time dt grid).status = 4 := by
  induction fuel generalizing dt with
  | zero => simp [retry]
  | succ fuel ih =>
    simp only [retry]
    split
    · split
      · simp
      · exact ih _
    · simp

theorem retry_success (fuel n : Nat) (time dt : UInt64) (grid : Array Cell)
    (h : (retry fuel n time dt grid).status = 0) :
    Time.validAdvance time (retry fuel n time dt grid).dt = true ∧
      accepted (retry fuel n time dt grid).grid = true ∧
      (retry fuel n time dt grid).grid =
        step n (Wasm.IEEE64.div (retry fuel n time dt grid).dt (Time.spacing n)) grid := by
  revert h
  induction fuel generalizing dt with
  | zero => simp [retry]
  | succ fuel ih =>
    simp only [retry]
    split
    · split
      · intro _
        exact ⟨by assumption, by assumption, rfl⟩
      · exact ih _
    · simp

theorem retry_indexed (fuel n : Nat) (time dt : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) (h : (retry fuel n time dt grid).status = 0) :
    Indexed n (retry fuel n time dt grid).grid := by
  rw [(retry_success fuel n time dt grid h).2.2]
  exact step_indexed n _ grid hg

theorem retry_asGrid (fuel n : Nat) (time dt : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) (h : (retry fuel n time dt grid).status = 0) :
    Numerics.step
        (Wasm.IEEE64.div (retry fuel n time dt grid).dt (Time.spacing n)) (asGrid n grid) =
      some (asGrid n (retry fuel n time dt grid).grid) := by
  obtain ⟨_, ha, he⟩ := retry_success fuel n time dt grid h
  rw [he] at ha ⊢
  exact step_asGrid n _ grid hg ha

#print axioms retry_status
#print axioms retry_success
#print axioms retry_indexed
#print axioms retry_asGrid

end Project.EulerRiemann.Control
