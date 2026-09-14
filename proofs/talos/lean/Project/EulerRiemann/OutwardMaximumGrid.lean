import Project.EulerRiemann.OutwardMaximumBounds

namespace Project.EulerRiemann.OutwardMaximum
open Project.ProofKit.F64Outward (Checked rejected)
open Project.ProofKit.F64Order
open Project.Euler2DCellStep.Sweep (orient)
open Traversal (Cell)
open CodeLib.IEEE64

theorem fold_status (cells : List Cell) (acc : Checked) :
    (cells.foldl scanCell acc).status = 0 ↔
      acc.status = 0 ∧ ∀ cell ∈ cells, (cellUpper cell.state).status = 0 := by
  induction cells generalizing acc with
  | nil => simp
  | cons cell cells ih =>
      simp only [List.foldl_cons, ih, scanCell, merge_status, List.mem_cons,
        forall_eq_or_imp]
      tauto

theorem fold_value (cells : List Cell) (acc : Checked)
    (h : (cells.foldl scanCell acc).status = 0) :
    (cells.foldl scanCell acc).value =
      (cells.map fun cell => (cellUpper cell.state).value).foldl max acc.value := by
  induction cells generalizing acc with
  | nil => rfl
  | cons cell cells ih =>
      simp only [List.foldl_cons, List.map_cons] at h ⊢
      have hs := (fold_status cells (scanCell acc cell)).mp h
      rw [ih _ h]
      change (cells.map fun cell => (cellUpper cell.state).value).foldl max
        (merge acc (cellUpper cell.state)).value = _
      rw [merge_value _ _ hs.1]

theorem fold_result (cells : List Cell) (acc : Checked)
    (ha : acc = rejected ∨ acc.status = 0) :
    cells.foldl scanCell acc = rejected ∨ (cells.foldl scanCell acc).status = 0 := by
  induction cells generalizing acc with
  | nil => exact ha
  | cons cell cells ih => exact ih _ (merge_result acc (cellUpper cell.state))

theorem grid_status (grid : Array Cell) :
    (gridUpper grid).status = 0 ↔ ∀ cell ∈ grid, (cellUpper cell.state).status = 0 := by
  simp only [gridUpper, ← Array.foldl_toList, fold_status, true_and,
    Array.mem_toList_iff]

theorem grid_values (grid : Array Cell) (h : (gridUpper grid).status = 0) :
    NonnegativeWord (gridUpper grid).value ∧
      ∀ cell ∈ grid, value (cellUpper cell.state).value ≤ value (gridUpper grid).value := by
  have hs := (grid_status grid).mp h
  have hw : ∀ word ∈ grid.toList.map (fun cell => (cellUpper cell.state).value),
      NonnegativeWord word := by
    intro word hword
    rcases List.mem_map.mp hword with ⟨cell, hc, rfl⟩
    exact Or.inr (cell_positive cell.state (hs cell (Array.mem_toList_iff.mp hc)))
  have hm := nonnegative_fold_max hw (Or.inl rfl : NonnegativeWord (0 : UInt64))
  have heq : (gridUpper grid).value =
      (grid.toList.map fun cell => (cellUpper cell.state).value).foldl max 0 := by
    simpa only [gridUpper, ← Array.foldl_toList] using
      fold_value grid.toList ⟨0, 0⟩ (by
        simpa only [gridUpper, ← Array.foldl_toList] using h)
  rw [heq]
  refine ⟨hm.1, ?_⟩
  intro cell hc
  exact hm.2.2 _ (List.mem_map.mpr ⟨cell, Array.mem_toList_iff.mpr hc, rfl⟩)

theorem grid_bounds (grid : Array Cell) (h : (gridUpper grid).status = 0) :
    CodeLib.IEEE64.Finite (gridUpper grid).value ∧
      ∀ cell ∈ grid, Bounds cell.state (gridUpper grid).value ∧
        Bounds (orient true cell.state) (gridUpper grid).value := by
  have hv := grid_values grid h
  refine ⟨(nonnegativeWord_spec hv.1).1, ?_⟩
  intro cell hc
  have hb := cell_bounds cell.state ((grid_status grid).mp h cell hc)
  exact ⟨bounds_mono hb.1 (hv.2 cell hc), bounds_mono hb.2 (hv.2 cell hc)⟩

theorem grid_behavior (grid : Array Cell) :
    gridUpper grid = rejected ∨
      (gridUpper grid).status = 0 ∧ CodeLib.IEEE64.Finite (gridUpper grid).value ∧
      ∀ cell ∈ grid, Bounds cell.state (gridUpper grid).value ∧
        Bounds (orient true cell.state) (gridUpper grid).value := by
  have hr : gridUpper grid = rejected ∨ (gridUpper grid).status = 0 := by
    simpa only [gridUpper, ← Array.foldl_toList] using
      fold_result grid.toList ⟨0, 0⟩ (Or.inr rfl)
  exact hr.imp_right (fun h => ⟨h, grid_bounds grid h⟩)

theorem grid_positive_of_mem (grid : Array Cell) (cell : Cell)
    (hc : cell ∈ grid) (h : (gridUpper grid).status = 0) :
    positiveBits (gridUpper grid).value = true := by
  have hv := grid_values grid h
  apply positiveBits_of_finite_value_pos _ (nonnegativeWord_spec hv.1).1
  exact (positiveBits_spec _ (cell_positive cell.state ((grid_status grid).mp h cell hc))).2.trans_le
    (hv.2 cell hc)

#print axioms grid_values
#print axioms grid_bounds
#print axioms grid_behavior
#print axioms grid_positive_of_mem

end Project.EulerRiemann.OutwardMaximum
