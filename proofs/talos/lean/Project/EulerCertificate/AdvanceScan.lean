import Project.EulerCertificate.AdvanceLoopShape

namespace Project.EulerCertificate.Execution
open Wasm Project.EulerRiemann

set_option maxRecDepth 32768

theorem advance_scan_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n : Nat) (fuel trials time source : UInt64) (boundary : Flux.Vector) (grid : Array Project.EulerRiemann.Traversal.Cell)
    (hParams : frame.params = advanceParams fuel n trials time source boundary)
    (hLocals : frame.locals.length = 157) (hValues : frame.values = [])
    (hGrid : Memory.GridAt store source grid) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store
      (advanceScanFrame frame source (OutwardMaximum.gridUpper grid)) env) :
    wp Project.EulerCertificate.«module» (advanceWorkBody.take 13 ++ rest) Q store frame env := by
  unfold advanceWorkBody advanceLoop func184
  dsimp only
  wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, advanceParams, Project.EulerCertificateFlux.Execution.vectorValues,
    Project.EulerCertificateFlux.Execution.boundsValues, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals, hValues]
  refine wp_call_tw (scan_exact env store source source grid hGrid) ?_
  rintro same values ⟨hSame, rfl⟩
  subst same
  wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, advanceParams, Project.EulerCertificateFlux.Execution.vectorValues,
    Project.EulerCertificateFlux.Execution.boundsValues, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, hParams, hLocals]
  simpa [advanceScanFrame, hParams, advanceParams,
    Project.EulerCertificateFlux.Execution.vectorValues, Project.EulerCertificateFlux.Execution.boundsValues] using hNext

#print axioms advance_scan_spec

end Project.EulerCertificate.Execution
