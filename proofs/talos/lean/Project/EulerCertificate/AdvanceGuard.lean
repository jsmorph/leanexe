import Project.EulerCertificate.AdvanceFrame

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768
open Project.EulerRiemann.Execution (boolWord)

macro "certificate_advance_guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [advanceParams, vectorValues, boundsValues, List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem advance_active_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source tracker outputTime outputRoot : UInt64) (boundary : Vector)
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot false boundary)
    (hFuel : fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store frame env) :
    wp Project.EulerCertificate.«module» (advanceLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_184_while_loop_0_guard_eq
  change some (advanceLoop.take 7) = some (Project.ProofKit.FuelGuard.program 0 35) at hShape
  rw [Option.some.inj hShape]
  apply Project.ProofKit.FuelGuard.program_spec 0 35 _ env store frame fuel 0 h.values
    (by simp [Locals.get, h.params, advanceParams])
    (by simpa [Locals.get, h.params, h.locals, boolWord, advanceParams, vectorValues, boundsValues] using h.done)
  simpa only [hFuel, ne_eq, not_false_eq_true, not_true_eq_false, or_self, ite_false] using hNext

theorem advance_completed_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source tracker outputTime outputRoot : UInt64) (boundary : Vector)
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot true boundary)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp Project.EulerCertificate.«module» (advanceLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_184_while_loop_0_guard_eq
  change some (advanceLoop.take 7) = some (Project.ProofKit.FuelGuard.program 0 35) at hShape
  rw [Option.some.inj hShape]
  apply Project.ProofKit.FuelGuard.program_spec 0 35 _ env store frame fuel 1 h.values
    (by simp [Locals.get, h.params, advanceParams])
    (by simpa [Locals.get, h.params, h.locals, boolWord, advanceParams, vectorValues, boundsValues] using h.done)
  simpa using hNext

theorem advance_time_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hLocals : frame.locals.length = 157) (hParams : frame.params.length = 18)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store (advanceTimeFrame frame) env) :
    wp Project.EulerCertificate.«module» ((advanceLoop.drop 7).take 2 ++ rest) Q store frame env := by
  unfold advanceLoop func184
  dsimp only
  have hCall := endTime_exact env store
  rw [← hValues] at hCall
  refine wp_call_tw hCall ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  certificate_advance_guard_peel
  simpa [advanceTimeFrame, hParams, hLocals] using hNext

theorem advance_finish_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source tracker outputTime outputRoot : UInt64) (done : Bool) (boundary : Vector)
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store (advanceReturnedFrame frame 0 time source boundary) env) :
    wp Project.EulerCertificate.«module» (advanceFinishBody ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  unfold advanceFinishBody advanceLoop func184
  dsimp only
  certificate_advance_guard_peel
  simpa [advanceReturnedFrame, hParams, advanceParams, vectorValues, boundsValues] using hNext

#print axioms advance_active_guard_spec
#print axioms advance_completed_guard_spec
#print axioms advance_time_spec
#print axioms advance_finish_spec

end Project.EulerCertificate.Execution
