import Project.EulerRiemann.AdvanceFrame

namespace Project.EulerRiemann.Execution
open Wasm

macro "advance_guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_active_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (time source tracker outputTime outputRoot : UInt64)
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot false)
    (hFuel : fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store frame env) :
    wp Project.EulerRiemann.«module» (advanceLoop.take 7 ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  have hDone := h.done
  rcases frame with ⟨params, locals, values⟩
  dsimp only at hParams hLocals hValues hDone hNext ⊢
  subst params
  subst values
  obtain ⟨hDoneBound, hDoneRead⟩ := List.getElem_of_getElem? hDone
  unfold advanceLoop func78
  dsimp only
  advance_guard_peel
  simpa [boolWord] using hNext

theorem advance_completed_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (time source tracker outputTime outputRoot : UInt64)
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot true)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp Project.EulerRiemann.«module» (advanceLoop.take 7 ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  have hDone := h.done
  rcases frame with ⟨params, locals, values⟩
  dsimp only at hParams hLocals hValues hDone hNext ⊢
  subst params
  subst values
  obtain ⟨hDoneBound, hDoneRead⟩ := List.getElem_of_getElem? hDone
  unfold advanceLoop func78
  dsimp only
  by_cases hFuel : fuel = 0 <;> advance_guard_peel <;>
    simpa [boolWord, hFuel] using hNext

theorem advance_time_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hLocals : frame.locals.length = 45) (hParams : frame.params.length = 5)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store (advanceTimeFrame frame) env) :
    wp Project.EulerRiemann.«module» ((advanceLoop.drop 7).take 2 ++ rest) Q store frame env := by
  unfold advanceLoop func78
  dsimp only
  have hCall := endTime_exact env store
  rw [← hValues] at hCall
  refine wp_call_tw hCall ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  advance_guard_peel
  simpa [advanceTimeFrame, hParams, hLocals] using hNext

theorem advance_finish_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (time source tracker outputTime outputRoot : UInt64) (done : Bool)
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store (advanceFinishedFrame frame time source) env) :
    wp Project.EulerRiemann.«module» (advanceFinishBody ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  unfold advanceFinishBody advanceLoop func78
  dsimp only
  advance_guard_peel
  simpa [advanceFinishedFrame, hParams] using hNext

#print axioms advance_active_guard_spec
#print axioms advance_completed_guard_spec
#print axioms advance_time_spec
#print axioms advance_finish_spec

end Project.EulerRiemann.Execution
