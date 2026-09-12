import Project.EulerRiemann.AcceptedLoop

namespace Project.EulerRiemann.Execution
open Wasm

theorem accepted_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerRiemann.«module» 72 initial
      [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Traversal.accepted grid))]) := by
  have hLength := hGrid.lengthRead
  have hBound := Nat.not_lt.mpr hGrid.lengthBound
  refine TerminatesWith.of_wp_entry_for (f := func72Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func72 _ initial
    (func72Def.toLocals [.i64 owner, .i64 pointer]) env
  rw [accepted_shape]
  unfold func72
  dsimp only
  wp_run [func72Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, List.nil_append,
    ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
    Nat.add_zero, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow,
    hLength, hBound]
  accepted_peel
  change wp _ _ _ initial
    (acceptedFrame owner pointer grid.size 0 true ⟨0, ⟨0, 0, 0, 0⟩, 0, 0⟩) env
  apply accepted_loop_spec env initial owner pointer grid hGrid 0 (Nat.zero_le _)
    (fun _ _ h => False.elim (by omega))
  intro index cell
  simp [wp_simp, acceptedFrame, boolWord]

#print axioms accepted_exact

end Project.EulerRiemann.Execution
