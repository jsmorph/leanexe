import Project.EulerReconstructed.NumericsModel
import Project.EulerRiemann.TraversalModel

namespace Project.EulerReconstructed.Traversal
open Project.Euler2DCellStep.Sweep
open Project.EulerRiemann.Traversal (Cell Indexed asGrid neighborIndex neighborIndex_eq linearIndex_lt)

theorem neighborIndex_x (n : Nat) (j i : Fin n) (forward : Bool) :
    neighborIndex n (j.val * n + i.val) false forward =
      j.val * n + (if forward then following i else previous i).val := by
  cases forward <;> simp only [neighborIndex_eq, Project.EulerRiemann.Geometry.neighbor_x
    n j.val i.val _ i.isLt, Bool.false_eq_true, ↓reduceIte, previous, following]

theorem neighborIndex_y (n : Nat) (j i : Fin n) (forward : Bool) :
    neighborIndex n (j.val * n + i.val) true forward =
      (if forward then following j else previous j).val * n + i.val := by
  cases forward <;> simp only [neighborIndex_eq, Project.EulerRiemann.Geometry.neighbor_y
    n j.val i.val _ j.isLt i.isLt, Bool.false_eq_true, ↓reduceIte, previous, following]

theorem cellStencil_eq (n : Nat) (axis : Bool) (grid : Array Cell)
    (j i : Fin n) (h : Indexed n grid) :
    cellStencil n axis grid grid[j.val * n + i.val]! =
      Numerics.inputs axis (asGrid n grid) j i := by
  have hi : j.val * n + i.val < grid.size := by
    rw [h.1]
    exact linearIndex_lt n j i
  have hind : grid[j.val * n + i.val]!.index = j.val * n + i.val := by
    rw [getElem!_pos grid _ hi]
    exact h.2 _ hi
  cases axis with
  | false =>
    simp only [cellStencil, hind, neighborIndex_x, Bool.false_eq_true, ↓reduceIte]
    rfl
  | true =>
    simp only [cellStencil, hind, neighborIndex_y, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem sweep_getElem (n fuel : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (i : Nat) (hi : i < grid.size) :
    (sweep n fuel axis ratio grid)[i]! = updateCell n fuel axis ratio grid grid[i]! := by
  simp [sweep, getElem!_pos, hi]

theorem sweep_asGrid (n fuel : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (h : Indexed n grid) :
    asGrid n (sweep n fuel axis ratio grid) =
      nextGrid axis (Numerics.outputs fuel ratio axis (asGrid n grid)) := by
  funext j i
  have hi : j.val * n + i.val < grid.size := by
    rw [h.1]
    exact linearIndex_lt n j i
  simp only [asGrid, sweep_getElem n fuel axis ratio grid _ hi, updateCell]
  rw [cellStencil_eq n axis grid j i h]
  rfl

theorem sweep_accepted_iff (n fuel : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (h : Indexed n grid) :
    Project.EulerRiemann.Traversal.accepted (sweep n fuel axis ratio grid) = true ↔
      Accepted (Numerics.outputs fuel ratio axis (asGrid n grid)) := by
  simp only [Project.EulerRiemann.Traversal.accepted, Array.all_eq_true, beq_iff_eq]
  constructor
  · intro ha j i
    have hi : j.val * n + i.val < grid.size := by
      rw [h.1]
      exact linearIndex_lt n j i
    have hs := ha (j.val * n + i.val) (by simpa [sweep] using hi)
    have he := cellStencil_eq n axis grid j i h
    simpa only [sweep, Array.getElem_map, updateCell,
      ← getElem!_pos grid (j.val * n + i.val) hi, he, Numerics.outputs, Numerics.evaluate] using hs
  · intro ha k hk
    have hk' : k < n * n := by simpa only [sweep_size, h.1] using hk
    have hn : 0 < n := by nlinarith
    let j : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk'⟩
    let i : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
    have heq : j.val * n + i.val = k := by
      simpa only [j, i, Nat.mul_comm] using Nat.div_add_mod k n
    have hi : k < grid.size := by simpa only [sweep_size] using hk
    have he := cellStencil_eq n axis grid j i h
    rw [heq] at he
    simpa only [sweep, Array.getElem_map, updateCell,
      ← getElem!_pos grid k hi, he, Numerics.outputs, Numerics.evaluate] using ha j i

#print axioms neighborIndex_x
#print axioms neighborIndex_y
#print axioms cellStencil_eq
#print axioms sweep_getElem
#print axioms sweep_asGrid
#print axioms sweep_accepted_iff
end Project.EulerReconstructed.Traversal
