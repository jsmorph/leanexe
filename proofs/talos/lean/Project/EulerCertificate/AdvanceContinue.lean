import Project.EulerCertificate.AdvanceGuard
import Project.EulerCertificate.AdvanceAccumulate
import Project.EulerCertificate.AdvanceTotalTrial

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
open Project.EulerRiemann.Execution (Heap)

local macro "certificate_advance_continue_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [advanceParams, advanceAccumulatedFrame, advanceTrialFrame, vectorValues, boundsValues, List.cons_append, List.nil_append, List.length_set,
        List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, f64Add,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_continue_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell)
    (n : Nat) (trials time alpha dt trialDt result : UInt64) (boundary stepBoundary : Vector) (tracked : Bool)
    (hParams : frame.params = advanceParams fuel n trials time source.root boundary)
    (hLocals : frame.locals.length = 157)
    (hTracker : frame.locals[0]? = some (.i64 (if tracked then source.root else 0)))
    (hSource : source.root ≠ 0) (hDifferent : source.root ≠ result)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q
      (if tracked then heap.releaseStore store source else store)
      (advanceContinuedFrame (advanceAccumulatedFrame
        (advanceTrialFrame frame n trials time source.root alpha dt trialDt result stepBoundary) boundary stepBoundary)
        fuel n trials (IEEE64.add time trialDt) result (Vectors.add boundary stepBoundary)) env) :
    wp Project.EulerCertificate.«module» (advanceContinueBody ++ rest) Q store
      (advanceTrialFrame frame n trials time source.root alpha dt trialDt result stepBoundary) env := by
  rw [← List.take_append_drop 109 advanceContinueBody, List.append_assoc]
  apply advance_accumulate_spec env store frame fuel n trials time source.root alpha dt trialDt result
    boundary stepBoundary hParams hLocals
  cases tracked with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hTracker hNext
    obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
    unfold advanceContinueBody advanceTrialBody advanceWorkBody advanceLoop func184
    dsimp only
    certificate_advance_continue_peel
    simpa [advanceContinuedFrame, advanceAccumulatedFrame, advanceTrialFrame, advanceParams, hParams, List.set] using hNext
  | true =>
    simp only [ite_true] at hTracker hNext
    obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
    unfold advanceContinueBody advanceTrialBody advanceWorkBody advanceLoop func184
    dsimp only
    certificate_advance_continue_peel
    refine wp_call_tw (release_owned env store heap source grid hHeap hOwner) ?_
    rintro final values ⟨rfl, hFinal, hFinalHeap⟩
    subst final
    certificate_advance_continue_peel
    simpa [advanceContinuedFrame, advanceAccumulatedFrame, advanceTrialFrame, advanceParams, hParams, List.set] using hNext

#print axioms advance_continue_spec

end Project.EulerCertificate.Execution
