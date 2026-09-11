import Project.EulerRiemann.TraversalInitial

namespace Project.EulerRiemann.Traversal
open Project.Euler2DCellStep.Sweep

def Indexed (n : Nat) (grid : Array Cell) : Prop :=
  grid.size = n * n ∧ ∀ i (h : i < grid.size), grid[i].index = i

def asGrid (n : Nat) (grid : Array Cell) : Grid n n :=
  fun j i => grid[j.val * n + i.val]!.state

theorem updateCell_index (n : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (cell : Cell) :
    (updateCell n axis ratio grid cell).index = cell.index := rfl

theorem sweep_size (n : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell) :
    (sweep n axis ratio grid).size = grid.size := by simp [sweep]

theorem sweep_indexed (n : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (h : Indexed n grid) : Indexed n (sweep n axis ratio grid) := by
  refine ⟨by simpa [sweep] using h.1, ?_⟩
  intro i hi
  simpa [sweep, updateCell_index] using h.2 i (by simpa [sweep] using hi)

theorem step_size (n : Nat) (ratio : UInt64) (grid : Array Cell) :
    (step n ratio grid).size = grid.size := by
  dsimp only [step]
  split <;> simp only [sweep_size]

theorem step_indexed (n : Nat) (ratio : UInt64) (grid : Array Cell)
    (h : Indexed n grid) : Indexed n (step n ratio grid) := by
  dsimp only [step]
  split
  · exact sweep_indexed n true ratio _ (sweep_indexed n false ratio grid h)
  · exact sweep_indexed n false ratio grid h

theorem updateCell_safe (n : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (cell : Cell)
    (h : (updateCell n axis ratio grid cell).status = 0) :
    StateSafe (updateCell n axis ratio grid cell).state := by
  have hs := (evaluate_safe ratio (cellInputs n axis grid cell) h).1
  exact orient_safe axis _ ⟨hs.bounds, hs.admissible⟩

theorem sweep_safe (n : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (h : accepted (sweep n axis ratio grid) = true) :
    ∀ i (hi : i < (sweep n axis ratio grid).size),
      StateSafe (sweep n axis ratio grid)[i].state := by
  have ha := Array.all_eq_true.mp h
  intro i hi
  have hi' : i < grid.size := by simpa [sweep] using hi
  have hs : (updateCell n axis ratio grid (grid[i]'hi')).status = 0 := by
    simpa [sweep] using ha i hi
  simpa [sweep] using updateCell_safe n axis ratio grid (grid[i]'hi') hs

theorem cellInputs_eq (n : Nat) (axis : Bool) (grid : Array Cell)
    (j i : Fin n) (h : Indexed n grid) :
    cellInputs n axis grid grid[j.val * n + i.val]! =
      inputs axis (asGrid n grid) j i := by
  have htotal : j.val * n + i.val < n * n := by
    have hm := Nat.mul_le_mul_right n (show j.val + 1 ≤ n by omega)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    omega
  have hi : j.val * n + i.val < grid.size := by rw [h.1]; exact htotal
  have hind : grid[j.val * n + i.val]!.index = j.val * n + i.val := by
    rw [getElem!_pos grid (j.val * n + i.val) hi]
    exact h.2 _ hi
  cases axis <;>
    simp only [cellInputs, hind, neighborIndex_eq, asGrid, inputs,
      Bool.false_eq_true, ↓reduceIte, previous, following]
  · rw [Geometry.neighbor_x n j.val i.val false i.isLt,
      Geometry.neighbor_x n j.val i.val true i.isLt]
    rfl
  · rw [Geometry.neighbor_y n j.val i.val false j.isLt i.isLt,
      Geometry.neighbor_y n j.val i.val true j.isLt i.isLt]
    rfl

#print axioms sweep_indexed
#print axioms step_indexed
#print axioms sweep_safe
#print axioms cellInputs_eq

end Project.EulerRiemann.Traversal
