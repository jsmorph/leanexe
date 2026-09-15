import Project.EulerReconstructed.ControlRetry
import Project.EulerRiemann.ControlSafe

namespace Project.EulerReconstructed.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell Indexed initialCells initialCells_indexed
  initialCells_getElem initialCell_safe)
open Project.EulerRiemann.Control (CellsSafe)
open Project.EulerReconstructed.Traversal (step_safe)

theorem retry_safe (fuel n trials : Nat) (time dt alpha : UInt64) (grid : Array Cell)
    (h : (retry fuel n trials time dt alpha grid).status = 0) :
    CellsSafe (retry fuel n trials time dt alpha grid).grid := by
  obtain ⟨_, _, ha, he⟩ := retry_success fuel n trials time dt alpha grid h
  rw [he] at ha ⊢
  exact step_safe n trials _ grid ha

theorem advance_terminal (fuel n trials : Nat) (time : UInt64) (grid : Array Cell) :
    (advance fuel n trials time grid).status = 0 →
      (advance fuel n trials time grid).time = Time.endTime := by
  induction fuel generalizing time grid with
  | zero =>
    simp only [advance]
    split
    · rename_i ht
      intro _
      simpa using ht
    · simp
  | succ fuel ih =>
    simp only [advance]
    split
    · rename_i ht
      intro _
      simpa using ht
    · split
      · split
        · exact ih _ _
        · rename_i ht hs ha
          intro h
          exact False.elim (ha (by simpa using h))
      · simp

theorem advance_indexed (fuel n trials : Nat) (time : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) : Indexed n (advance fuel n trials time grid).grid := by
  induction fuel generalizing time grid with
  | zero => exact hg
  | succ fuel ih =>
    simp only [advance]
    split
    · exact hg
    · split
      · split
        · rename_i ht hs ha
          exact ih _ _ (retry_indexed _ _ _ _ _ _ _ hg (by simpa using ha))
        · exact hg
      · exact hg

theorem advance_safe (fuel n trials : Nat) (time : UInt64) (grid : Array Cell)
    (hg : CellsSafe grid) : CellsSafe (advance fuel n trials time grid).grid := by
  induction fuel generalizing time grid with
  | zero => exact hg
  | succ fuel ih =>
    simp only [advance]
    split
    · exact hg
    · split
      · split
        · rename_i ht hs ha
          exact ih _ _ (retry_safe _ _ _ _ _ _ _ (by simpa using ha))
        · exact hg
      · exact hg

theorem run_indexed (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : Indexed n (run n trials).grid := by
  simp only [run, hn]
  exact advance_indexed _ n trials 0 _ (initialCells_indexed n hn)

theorem run_safe (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : CellsSafe (run n trials).grid := by
  simp only [run, hn]
  apply advance_safe
  intro i hi
  rw [initialCells_getElem n hn i hi]
  exact initialCell_safe n i

theorem run_terminal (n trials : Nat) (h : (run n trials).status = 0) :
    (run n trials).time = Time.endTime := by
  revert h
  simp only [run]
  split
  · exact advance_terminal _ _ _ _ _
  · simp

theorem solve_size (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    (solve n trials).size = 4 + 2 * (n * n) :=
  Output.pack_indexed_size n _ _ _ (run_indexed n trials hn)

#print axioms retry_safe
#print axioms advance_terminal
#print axioms advance_indexed
#print axioms advance_safe
#print axioms run_indexed
#print axioms run_safe
#print axioms run_terminal
#print axioms solve_size
end Project.EulerReconstructed.Control
