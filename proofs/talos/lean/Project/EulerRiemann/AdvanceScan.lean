import Project.EulerRiemann.AdvanceLoopShape

namespace Project.EulerRiemann.Execution
open Wasm

theorem advance_scan_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (fuel time source : UInt64) (grid : Array Traversal.Cell)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 45) (hValues : frame.values = [])
    (hGrid : Memory.GridAt store source grid) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (advanceScanFrame frame source (Traversal.scan grid)) env) :
    wp Project.EulerRiemann.«module» (advanceWorkBody.take 13 ++ rest) Q store frame env := by
  unfold advanceWorkBody advanceLoop func78
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

end Project.EulerRiemann.Execution
