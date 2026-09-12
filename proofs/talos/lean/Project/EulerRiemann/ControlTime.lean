import Project.EulerRiemann.ControlRetry
import Project.EulerRiemann.OutputModel

namespace Project.EulerRiemann.Control
open Traversal

theorem advance_terminal (fuel n : Nat) (time : UInt64) (grid : Array Cell) :
    (advance fuel n time grid).status = 0 →
      (advance fuel n time grid).time = Time.endTime := by
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

theorem advance_indexed (fuel n : Nat) (time : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) : Indexed n (advance fuel n time grid).grid := by
  induction fuel generalizing time grid with
  | zero => exact hg
  | succ fuel ih =>
    simp only [advance]
    split
    · exact hg
    · split
      · split
        · rename_i ht hs ha
          exact ih _ _ (retry_indexed _ _ _ _ _ hg (by simpa using ha))
        · exact hg
      · exact hg

theorem run_indexed (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : Indexed n (run n).grid := by
  simp only [run, hn, ↓reduceIte]
  exact advance_indexed _ n 0 _ (initialCells_indexed n hn)

theorem run_terminal (n : Nat) (h : (run n).status = 0) :
    (run n).time = Time.endTime := by
  revert h
  simp only [run]
  split
  · exact advance_terminal _ _ _ _
  · simp

theorem solve_size (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    (solve n).size = 4 + 2 * (n * n) := by
  exact Output.pack_indexed_size n _ _ _ (run_indexed n hn)

#print axioms advance_terminal
#print axioms advance_indexed
#print axioms run_indexed
#print axioms run_terminal
#print axioms solve_size

end Project.EulerRiemann.Control
