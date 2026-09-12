import Project.EulerRiemann.RetryFrame
import Project.EulerRiemann.AnnotationMatches

namespace Project.EulerRiemann.Execution
open Wasm

macro "retry_guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem retry_validity_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (time dt source outputDt outputRoot : UInt64) (done : Bool)
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot done)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (retryGuardFrame frame time dt (Time.validAdvance time dt)) env) :
    wp Project.EulerRiemann.«module» ((retryLoop.drop 7).take 8 ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  unfold retryLoop func74
  dsimp only
  retry_guard_peel
  refine wp_call_tw (validAdvance_exact env store time dt) ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  retry_guard_peel
  simpa [retryGuardFrame, boolWord, hParams] using hNext

theorem retry_active_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (time dt source outputDt outputRoot : UInt64)
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot false)
    (hFuel : fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store frame env) :
    wp Project.EulerRiemann.«module» (retryLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_74_while_loop_0_guard_eq
  change some (retryLoop.take 7) = some (Project.ProofKit.FuelGuard.program 0 11) at hShape
  rw [Option.some.inj hShape]
  apply Project.ProofKit.FuelGuard.program_spec 0 11 _ env store frame fuel 0 h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals, boolWord] using h.done)
  simpa only [hFuel, ne_eq, not_false_eq_true, not_true_eq_false, or_self, ite_false] using hNext

theorem retry_completed_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (time dt source outputDt outputRoot : UInt64)
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot true)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp Project.EulerRiemann.«module» (retryLoop.take 7 ++ rest) Q store frame env := by
  have hShape := AnnotationMatches.function_74_while_loop_0_guard_eq
  change some (retryLoop.take 7) = some (Project.ProofKit.FuelGuard.program 0 11) at hShape
  rw [Option.some.inj hShape]
  apply Project.ProofKit.FuelGuard.program_spec 0 11 _ env store frame fuel 1 h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals, boolWord] using h.done)
  simpa using hNext

#print axioms retry_validity_spec
#print axioms retry_active_guard_spec
#print axioms retry_completed_guard_spec

end Project.EulerRiemann.Execution
