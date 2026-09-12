import Project.EulerRiemann.ControlTime

namespace Project.EulerRiemann.Control
open Traversal
open Project.Euler2DCellStep.Sweep (StateSafe)

noncomputable def CellsSafe (grid : Array Cell) : Prop :=
  ∀ i (hi : i < grid.size), StateSafe grid[i].state

theorem step_safe (n : Nat) (ratio : UInt64) (grid : Array Cell)
    (h : accepted (step n ratio grid) = true) : CellsSafe (step n ratio grid) := by
  revert h
  dsimp only [step]
  split
  · exact sweep_safe n true ratio _
  · exact sweep_safe n false ratio grid

theorem retry_safe (fuel n : Nat) (time dt : UInt64) (grid : Array Cell)
    (h : (retry fuel n time dt grid).status = 0) :
    CellsSafe (retry fuel n time dt grid).grid := by
  obtain ⟨_, ha, he⟩ := retry_success fuel n time dt grid h
  rw [he] at ha ⊢
  exact step_safe n _ grid ha

theorem advance_safe (fuel n : Nat) (time : UInt64) (grid : Array Cell)
    (hg : CellsSafe grid) : CellsSafe (advance fuel n time grid).grid := by
  induction fuel generalizing time grid with
  | zero => exact hg
  | succ fuel ih =>
    simp only [advance]
    split
    · exact hg
    · split
      · split
        · rename_i ht hs ha
          exact ih _ _ (retry_safe _ _ _ _ _ (by simpa using ha))
        · exact hg
      · exact hg

theorem run_safe (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : CellsSafe (run n).grid := by
  simp only [run, hn]
  apply advance_safe
  intro i hi
  rw [initialCells_getElem n hn i hi]
  exact initialCell_safe n i

#print axioms step_safe
#print axioms retry_safe
#print axioms advance_safe
#print axioms run_safe

end Project.EulerRiemann.Control
