import Project.EulerRiemann.ScanLoop

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def scanHead : Wasm.Program := func25.take 25
def scanTail : Wasm.Program := func25.drop 26

theorem scan_shape :
    func25 = scanHead ++ [.block 0 0 [.loop 0 0 scanLoop]] ++ scanTail := rfl

theorem scan_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerRiemann.«module» 25 initial
      [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (Traversal.scan grid).alpha, .i64 (Traversal.scan grid).status]) := by
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func25 _ initial
    (func25Def.toLocals [.i64 owner, .i64 pointer]) env
  rw [scan_shape]
  unfold scanHead func25
  dsimp only
  wp_run [func25Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, List.nil_append,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow,
    hLength, hBound]
  scan_peel
  change wp _ _ _ _
    (scanFrame owner pointer grid.size 0 ⟨0, 0⟩ { borrowed := pointer }) _
  nth_rw 1 [← scanPrefix_zero grid]
  apply scan_loop_spec env initial owner pointer grid hGrid 0 (Nat.zero_le _)
    { borrowed := pointer }
  intro scratch
  unfold func25
  dsimp only
  scan_peel
  simp [scanPrefix_size]

#print axioms scan_shape
#print axioms scan_exact

end Project.EulerRiemann.Execution
