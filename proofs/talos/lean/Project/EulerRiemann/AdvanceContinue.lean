import Project.EulerRiemann.AdvanceGuard
import Project.EulerRiemann.AdvanceTrial

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

local macro "advance_continue_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [advanceTrialFrame, List.cons_append, List.nil_append, List.length_set,
        List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ, f64Add,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_continue_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (source : FreeNode) (grid : Array Traversal.Cell)
    (n : Nat) (time alpha dt trialDt result : UInt64) (tracked : Bool)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
      .i64 source.root, .i64 source.root])
    (hLocals : frame.locals.length = 45)
    (hTracker : frame.locals[0]? = some (.i64 (if tracked then source.root else 0)))
    (hSource : source.root ≠ 0) (hDifferent : source.root ≠ result)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q
      (if tracked then heap.releaseStore store source else store)
      (advanceContinuedFrame (advanceTrialFrame frame n time source.root alpha dt trialDt result)
        fuel n (IEEE64.add time trialDt) result) env) :
    wp Project.EulerRiemann.«module» (advanceContinueBody ++ rest) Q store
      (advanceTrialFrame frame n time source.root alpha dt trialDt result) env := by
  cases tracked with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hTracker hNext
    obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
    unfold advanceContinueBody advanceTrialBody advanceWorkBody advanceLoop func78
    dsimp only
    advance_continue_peel
    simpa [advanceContinuedFrame, advanceTrialFrame, hParams, List.set] using hNext
  | true =>
    simp only [ite_true] at hTracker hNext
    obtain ⟨hTrackerBound, hTrackerRead⟩ := List.getElem_of_getElem? hTracker
    unfold advanceContinueBody advanceTrialBody advanceWorkBody advanceLoop func78
    dsimp only
    advance_continue_peel
    refine wp_call_tw (release_owned env store heap source grid hHeap hOwner) ?_
    rintro final values ⟨rfl, hFinal, hFinalHeap⟩
    subst final
    advance_continue_peel
    simpa [advanceContinuedFrame, advanceTrialFrame, hParams, List.set] using hNext

#print axioms advance_continue_spec

end Project.EulerRiemann.Execution
