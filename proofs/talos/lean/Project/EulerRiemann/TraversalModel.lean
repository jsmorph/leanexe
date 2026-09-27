import Project.EulerRiemann.TraversalSweep

namespace Project.EulerRiemann.Traversal
open Project.Euler2DCellStep.Sweep

theorem linearIndex_lt (n : Nat) (j i : Fin n) : j.val * n + i.val < n * n := by
  have hm := Nat.mul_le_mul_right n (show j.val + 1 ≤ n by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem initialCells_getElem (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800)
    (i : Nat) (hi : i < (initialCells n).size) :
    (initialCells n)[i] = initialCell n i := by
  simp only [← Array.getElem_toList, initialCells_toList n hn,
    List.getElem_map, List.getElem_range]

theorem initialCells_indexed (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    Indexed n (initialCells n) := by
  refine ⟨initialCells_size n hn, ?_⟩
  intro i hi
  rw [initialCells_getElem n hn i hi, initialCell_index]

theorem initialCells_asGrid (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    asGrid n (initialCells n) = Initial.initial n := by
  funext j i
  have hbound : j.val * n + i.val < (initialCells n).size := by
    rw [initialCells_size n hn]
    exact linearIndex_lt n j i
  have hmod : (j.val * n + i.val) % n = i.val := Nat.mul_add_mod_of_lt i.isLt
  have hdiv : (j.val * n + i.val) / n = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  simp only [asGrid, getElem!_pos (initialCells n) (j.val * n + i.val) hbound,
    initialCells_getElem n hn,
    initialCell, Initial.initial, hmod, hdiv,
    LeanExe.Examples.EulerRiemann.lowerFractionNumerator]

theorem sweep_getElem (n : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (i : Nat) (hi : i < grid.size) :
    (sweep n axis ratio grid)[i]! = updateCell n axis ratio grid grid[i]! := by
  simp [sweep, getElem!_pos, hi]

theorem sweep_asGrid (n : Nat) (axis : Bool) (ratio : UInt64) (grid : Array Cell)
    (h : Indexed n grid) :
    asGrid n (sweep n axis ratio grid) =
      nextGrid axis (Numerics.outputs ratio axis (asGrid n grid)) := by
  funext j i
  have hi : j.val * n + i.val < grid.size := by
    rw [h.1]
    exact linearIndex_lt n j i
  simp only [asGrid, sweep_getElem n axis ratio grid _ hi, updateCell]
  rw [cellInputs_eq n axis grid j i h]
  rfl

theorem sweep_accepted_iff (n : Nat) (axis : Bool) (ratio : UInt64)
    (grid : Array Cell) (h : Indexed n grid) :
    accepted (sweep n axis ratio grid) = true ↔
      Accepted (Numerics.outputs ratio axis (asGrid n grid)) := by
  simp only [accepted, Array.all_eq_true, beq_iff_eq]
  constructor
  · intro ha j i
    have hi : j.val * n + i.val < grid.size := by
      rw [h.1]
      exact linearIndex_lt n j i
    have hs := ha (j.val * n + i.val) (by simpa [sweep] using hi)
    have he := cellInputs_eq n axis grid j i h
    simpa only [sweep, Array.getElem_map, updateCell,
      ← getElem!_pos grid (j.val * n + i.val) hi, he, Numerics.outputs] using hs
  · intro ha k hk
    have hk' : k < n * n := by simpa only [sweep_size, h.1] using hk
    have hn : 0 < n := by nlinarith
    let j : Fin n := ⟨k / n, (Nat.div_lt_iff_lt_mul hn).mpr hk'⟩
    let i : Fin n := ⟨k % n, Nat.mod_lt k hn⟩
    have heq : j.val * n + i.val = k := by
      simpa only [j, i, Nat.mul_comm] using Nat.div_add_mod k n
    have hi : k < grid.size := by simpa only [sweep_size] using hk
    have he := cellInputs_eq n axis grid j i h
    rw [heq] at he
    simpa only [sweep, Array.getElem_map, updateCell,
      ← getElem!_pos grid k hi, he, Numerics.outputs] using ha j i

theorem step_asGrid (n : Nat) (ratio : UInt64) (grid : Array Cell)
    (h : Indexed n grid) (ha : accepted (step n ratio grid) = true) :
    Numerics.step ratio (asGrid n grid) =
      some (asGrid n (step n ratio grid)) := by
  have hx : accepted (sweep n false ratio grid) = true := by
    by_contra hx
    simp only [step, hx, ↓reduceIte] at ha
  have hxs := (sweep_accepted_iff n false ratio grid h).mp hx
  have hm := sweep_indexed n false ratio grid h
  have hy : accepted (sweep n true ratio (sweep n false ratio grid)) = true := by
    simpa only [step, hx, ↓reduceIte] using ha
  have hys := (sweep_accepted_iff n true ratio _ hm).mp hy
  rw [sweep_asGrid n false ratio grid h] at hys
  simp only [Numerics.step, hxs, hys, ↓reduceIte,
    step, hx, sweep_asGrid n true ratio _ hm, sweep_asGrid n false ratio grid h]

#print axioms initialCells_indexed
#print axioms initialCells_asGrid
#print axioms sweep_asGrid
#print axioms sweep_accepted_iff
#print axioms step_asGrid

end Project.EulerRiemann.Traversal
