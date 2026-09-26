import Project.EulerReconstructed.FrozenTraversal
import Project.EulerRiemann.FrozenReconstructedStepSpec
import Project.EulerRiemann.FrozenTraversalSweep

namespace Project.EulerReconstructed.Frozen.Traversal
open Project.EulerRiemann.Frozen.Traversal (Cell Indexed accepted)
open Project.Euler2DCellStep.Sweep (StateSafe orient_safe)

theorem sweep_size (n fuel : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell) :
    (sweep n fuel axis ratio grid).size = grid.size := by simp [sweep]

theorem sweep_indexed (n fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (h : Indexed n grid) : Indexed n (sweep n fuel axis ratio grid) := by
  refine ⟨by simpa [sweep] using h.1, ?_⟩
  intro i hi
  simpa [sweep, updateCell] using h.2 i (by simpa [sweep] using hi)

theorem step_size (n fuel : Nat) (ratio : UInt64) (grid : Array Cell) :
    (step n fuel ratio grid).size = grid.size := by
  dsimp only [step]
  split <;> simp only [sweep_size]

theorem step_indexed (n fuel : Nat) (ratio : UInt64) (grid : Array Cell)
    (h : Indexed n grid) : Indexed n (step n fuel ratio grid) := by
  dsimp only [step]
  split
  · exact sweep_indexed n fuel true ratio _ (sweep_indexed n fuel false ratio grid h)
  · exact sweep_indexed n fuel false ratio grid h

theorem updateCell_safe (n fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (cell : Cell) (h : (updateCell n fuel axis ratio grid cell).status = 0) :
    StateSafe (updateCell n fuel axis ratio grid cell).state := by
  let input := cellStencil n axis grid cell
  have hb := (Project.EulerRiemann.Frozen.OutwardNumerics.reconstructed_step_state fuel ratio
    input.farLeft input.left input.center input.right input.farRight h).1
  exact orient_safe axis _ ⟨hb, hb.densityPositive, mul_pos (by norm_num) hb.internalPositive⟩

theorem sweep_safe (n fuel : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (h : accepted (sweep n fuel axis ratio grid) = true) :
    ∀ i (hi : i < (sweep n fuel axis ratio grid).size),
      StateSafe (sweep n fuel axis ratio grid)[i].state := by
  have ha := Array.all_eq_true.mp h
  intro i hi
  have hi' : i < grid.size := by simpa [sweep] using hi
  have hs : (updateCell n fuel axis ratio grid (grid[i]'hi')).status = 0 := by
    simpa [sweep] using ha i hi
  simpa [sweep] using updateCell_safe n fuel axis ratio grid (grid[i]'hi') hs

theorem step_safe (n fuel : Nat) (ratio : UInt64) (grid : Array Cell)
    (h : accepted (step n fuel ratio grid) = true) :
    ∀ i (hi : i < (step n fuel ratio grid).size), StateSafe (step n fuel ratio grid)[i].state := by
  revert h
  dsimp only [step]
  split
  · exact sweep_safe n fuel true ratio _
  · exact sweep_safe n fuel false ratio grid

#print axioms sweep_indexed
#print axioms step_indexed
#print axioms updateCell_safe
#print axioms sweep_safe
#print axioms step_safe
end Project.EulerReconstructed.Frozen.Traversal
