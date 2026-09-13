import Project.EulerRiemann.Traversal

namespace Project.EulerRiemann.Traversal
open Numerics (sideCheckedBits)

theorem word_or_zero (a b : UInt64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [UInt64.eq_iff_toBitVec_eq, UInt64.toBitVec_or, UInt64.toBitVec_ofNat,
    BitVec.or_eq_zero_iff]

theorem word_max_le (a b bound : UInt64) :
    max a b ≤ bound ↔ a ≤ bound ∧ b ≤ bound := by
  change (if a ≤ b then b else a) ≤ bound ↔ a ≤ bound ∧ b ≤ bound
  split <;> simp_all only [UInt64.le_iff_toNat_le] <;> omega

def SidesAccepted (cell : Cell) : Prop :=
  (sideCheckedBits cell.state.density cell.state.mx cell.state.my cell.state.energy).status = 0 ∧
  (sideCheckedBits cell.state.density cell.state.my cell.state.mx cell.state.energy).status = 0

def speed (cell : Cell) : UInt64 :=
  max (sideCheckedBits cell.state.density cell.state.mx cell.state.my cell.state.energy).speed
    (sideCheckedBits cell.state.density cell.state.my cell.state.mx cell.state.energy).speed

theorem fold_status (cells : List Cell) (acc : Scan) :
    (cells.foldl scanCell acc).status = 0 ↔
      acc.status = 0 ∧ ∀ cell ∈ cells, SidesAccepted cell := by
  induction cells generalizing acc with
  | nil => simp
  | cons cell cells ih =>
    simp only [List.foldl_cons, ih, scanCell, word_or_zero, List.mem_cons,
      forall_eq_or_imp, SidesAccepted]
    tauto

theorem fold_alpha_le (cells : List Cell) (acc : Scan) (bound : UInt64) :
    (cells.foldl scanCell acc).alpha ≤ bound ↔
      acc.alpha ≤ bound ∧ ∀ cell ∈ cells, speed cell ≤ bound := by
  induction cells generalizing acc with
  | nil => simp
  | cons cell cells ih =>
    simp only [List.foldl_cons, ih, scanCell, word_max_le, List.mem_cons,
      forall_eq_or_imp, speed]
    tauto

theorem scan_status (grid : Array Cell) :
    (scan grid).status = 0 ↔ ∀ cell ∈ grid, SidesAccepted cell := by
  simpa only [scan, ← Array.foldl_toList, fold_status, true_and, Array.mem_toList_iff]

theorem scan_alpha_le (grid : Array Cell) (bound : UInt64) :
    (scan grid).alpha ≤ bound ↔ ∀ cell ∈ grid, speed cell ≤ bound := by
  have hzero : (0 : UInt64) ≤ bound := by
    apply UInt64.le_iff_toNat_le.mpr
    simp
  simpa only [scan, ← Array.foldl_toList, fold_alpha_le, hzero, true_and,
    Array.mem_toList_iff]

theorem speed_le_scan (grid : Array Cell) (cell : Cell) (h : cell ∈ grid) :
    speed cell ≤ (scan grid).alpha :=
  (scan_alpha_le grid (scan grid).alpha).mp (UInt64.le_refl _) cell h

#print axioms scan_status
#print axioms scan_alpha_le
#print axioms speed_le_scan

end Project.EulerRiemann.Traversal
