import Project.EulerReconstructed.FrozenAdvanceFrame

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm
open Project.EulerRiemann.Frozen.Execution (boolWord)

macro "reconstructed_advance_guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_active_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source tracker outputTime outputRoot : UInt64)
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot false)
    (hFuel : fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store frame env) :
    wp Project.EulerReconstructed.Frozen.«module» (advanceLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_129_while_loop_0_guard_eq
  change some (advanceLoop.take 7) = some (Project.ProofKit.FuelGuard.program 0 11) at hShape
  rw [Option.some.inj hShape]
  apply Project.ProofKit.FuelGuard.program_spec 0 11 _ env store frame fuel 0 h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals, boolWord] using h.done)
  simpa only [hFuel, ne_eq, not_false_eq_true, not_true_eq_false, or_self, ite_false] using hNext

theorem advance_completed_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source tracker outputTime outputRoot : UInt64)
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot true)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp Project.EulerReconstructed.Frozen.«module» (advanceLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_129_while_loop_0_guard_eq
  change some (advanceLoop.take 7) = some (Project.ProofKit.FuelGuard.program 0 11) at hShape
  rw [Option.some.inj hShape]
  apply Project.ProofKit.FuelGuard.program_spec 0 11 _ env store frame fuel 1 h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals, boolWord] using h.done)
  simpa using hNext

theorem advance_time_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hLocals : frame.locals.length = 49) (hParams : frame.params.length = 6)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store (advanceTimeFrame frame) env) :
    wp Project.EulerReconstructed.Frozen.«module» ((advanceLoop.drop 7).take 2 ++ rest) Q store frame env := by
  unfold advanceLoop func129
  dsimp only
  have hCall := endTime_exact env store
  rw [← hValues] at hCall
  refine wp_call_tw hCall ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  reconstructed_advance_guard_peel
  simpa [advanceTimeFrame, hParams, hLocals] using hNext

theorem advance_finish_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source tracker outputTime outputRoot : UInt64) (done : Bool)
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerReconstructed.Frozen.«module» rest Q store (advanceFinishedFrame frame time source) env) :
    wp Project.EulerReconstructed.Frozen.«module» (advanceFinishBody ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  unfold advanceFinishBody advanceLoop func129
  dsimp only
  reconstructed_advance_guard_peel
  simpa [advanceFinishedFrame, hParams] using hNext

#print axioms advance_active_guard_spec
#print axioms advance_completed_guard_spec
#print axioms advance_time_spec
#print axioms advance_finish_spec

end Project.EulerReconstructed.Frozen.Execution
