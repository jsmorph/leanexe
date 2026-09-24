import Project.EulerReconstructed.FrozenAdvanceLoopShape

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.EulerRiemann.Frozen

theorem advance_scan_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (fuel trials time source : UInt64) (grid : Array Project.EulerRiemann.Frozen.Traversal.Cell)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 49) (hValues : frame.values = [])
    (hGrid : Memory.GridAt store source grid) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store
      (advanceScanFrame frame source (OutwardMaximum.gridUpper grid)) env) :
    wp Project.EulerReconstructed.Frozen.«module» (advanceWorkBody.take 13 ++ rest) Q store frame env := by
  unfold advanceWorkBody advanceLoop func129
  dsimp only
  wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals, hValues]
  refine wp_call_tw (scan_exact env store source source grid hGrid) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals]
  simpa [advanceScanFrame, hParams] using hNext

#print axioms advance_scan_spec

end Project.EulerReconstructed.Frozen.Execution
