import Project.EulerCertificate.AdvanceFrame

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

theorem advance_accumulate_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source alpha dt trialDt result : UInt64)
    (boundary stepBoundary : Vector)
    (hParams : frame.params = advanceParams fuel n trials time source boundary)
    (hLocals : frame.locals.length = 157) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store
      (advanceAccumulatedFrame (advanceTrialFrame frame n trials time source alpha dt trialDt result stepBoundary)
        boundary stepBoundary) env) :
    wp module (advanceContinueBody.take 109 ++ rest) Q store
      (advanceTrialFrame frame n trials time source alpha dt trialDt result stepBoundary) env := by
  unfold advanceContinueBody advanceTrialBody advanceWorkBody advanceLoop func184
  dsimp only
  wp_run [advanceTrialFrame, advanceParams, vectorValues, boundsValues, hParams, hLocals,
    List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  refine wp_call_tw (vector_add_exact env store boundary stepBoundary) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_run [advanceTrialFrame, advanceParams, vectorValues, boundsValues, hParams, hLocals,
    List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff]
  simpa [advanceAccumulatedFrame, advanceTrialFrame, advanceParams, vectorValues, boundsValues, hParams] using hNext

#print axioms advance_accumulate_spec
end Project.EulerCertificate.Execution
