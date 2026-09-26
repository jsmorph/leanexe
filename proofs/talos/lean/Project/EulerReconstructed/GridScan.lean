import Project.EulerReconstructed.ScanLoop
import Project.EulerReconstructed.AnnotationMatches

namespace Project.EulerReconstructed.Execution
open Wasm
open Project.EulerOutwardGrid.Execution (scanPrefix_zero scanPrefix_size)
open Project.EulerRiemann
open Project.ProofKit.F64Outward (Checked)
open Project.EulerOutwardSpeed.Execution (checkedValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def scanHead : Wasm.Program := func46.take 23
def scanTail : Wasm.Program := func46.drop 24

theorem scan_shape :
    func46 = scanHead ++ [.block 0 0 [.loop 0 0 scanLoop]] ++ scanTail := by
  calc
    func46 = AnnotationMatches.function_46_array_fold_0_program ++ func46.drop 28 :=
      AnnotationMatches.function_46_array_fold_0_tail_eq
    _ = scanHead ++ [.block 0 0 [.loop 0 0 scanLoop]] ++ scanTail := rfl

theorem scan_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerReconstructed.«module» 46 initial
      [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (OutwardMaximum.gridUpper grid).value, .i64 (OutwardMaximum.gridUpper grid).status]) := by
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  refine TerminatesWith.of_wp_entry_for (f := func46Def) rfl ?_ (by decide)
  change wp Project.EulerReconstructed.«module» func46 _ initial
    (func46Def.toLocals [.i64 owner, .i64 pointer]) env
  rw [scan_shape]
  unfold scanHead func46
  dsimp only
  wp_run [func46Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, List.nil_append,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow,
    hLength, hBound]
  reconstructed_scan_peel
  change wp _ _ _ _
    (scanFrame owner pointer grid.size 0 ⟨0, 0⟩ { borrowed := pointer }) _
  nth_rw 1 [← scanPrefix_zero grid]
  apply scan_loop_spec env initial owner pointer grid hGrid 0 (Nat.zero_le _)
    { borrowed := pointer }
  intro scratch
  unfold func46
  dsimp only
  reconstructed_scan_peel
  simp [scanPrefix_size]

#print axioms scan_shape
#print axioms scan_exact

end Project.EulerReconstructed.Execution
