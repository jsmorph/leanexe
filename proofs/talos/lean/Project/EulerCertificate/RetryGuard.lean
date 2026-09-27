import Project.EulerCertificate.RetryFrame

namespace Project.EulerCertificate.Execution
open Wasm Project.EulerRiemann
open Project.EulerRiemann.Execution (boolWord)

macro "certificate_retry_guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [List.cons_append, List.nil_append, List.length_set, List.getElem?_set,
        List.getElem?_cons_zero, List.getElem?_cons_succ, boolWord, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem retry_validity_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source outputDt outputRoot : UInt64) (done : Bool)
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store
      (retryGuardFrame frame time dt (Time.validAdvance time dt)) env) :
    wp Project.EulerCertificate.«module» ((retryLoop.drop 7).take 8 ++ rest) Q store frame env := by
  have hParams := h.params
  have hLocals := h.locals
  have hValues := h.values
  unfold retryLoop func179
  dsimp only
  certificate_retry_guard_peel
  refine wp_call_tw (validAdvance_exact env store time dt) ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  certificate_retry_guard_peel
  simpa [retryGuardFrame, boolWord, hParams] using hNext

theorem retry_active_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source outputDt outputRoot : UInt64)
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot false)
    (hFuel : fuel ≠ 0) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerCertificate.«module» rest Q store frame env) :
    wp Project.EulerCertificate.«module» (retryLoop.take 7 ++ rest) Q store frame env := by
  rw [retry_guard_shape]
  apply Project.ProofKit.FuelGuard.program_spec 0 25 _ env store frame fuel 0 h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals, boolWord] using h.done)
  simpa only [hFuel, ne_eq, not_false_eq_true, not_true_eq_false, or_self, ite_false] using hNext

theorem retry_completed_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time dt alpha source outputDt outputRoot : UInt64)
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot true)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp Project.EulerCertificate.«module» (retryLoop.take 7 ++ rest) Q store frame env := by
  rw [retry_guard_shape]
  apply Project.ProofKit.FuelGuard.program_spec 0 25 _ env store frame fuel 1 h.values
    (by simp [Locals.get, h.params])
    (by simpa [Locals.get, h.params, h.locals, boolWord] using h.done)
  simpa using hNext

theorem retry_returned_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status dt root : UInt64) (boundary : Project.EulerCertificate.Flux.Vector)
    (h : RetryReturnedAt frame status dt root boundary)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp Project.EulerCertificate.«module» (retryLoop.take 7 ++ rest) Q store frame env := by
  obtain ⟨fuel, hFuel⟩ := h.fuel
  rw [retry_guard_shape]
  apply Project.ProofKit.FuelGuard.program_spec 0 25 _ env store frame fuel 1 h.values
    (by simpa [Locals.get, h.params] using hFuel)
    (by simpa [Locals.get, h.params, h.locals] using h.done)
  simpa using hNext

#print axioms retry_returned_guard_spec
#print axioms retry_validity_spec
#print axioms retry_active_guard_spec
#print axioms retry_completed_guard_spec

end Project.EulerCertificate.Execution
