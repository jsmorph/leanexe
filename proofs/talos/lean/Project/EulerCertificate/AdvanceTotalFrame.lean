import Project.EulerCertificate.AdvanceGuard

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768

structure AdvanceReturnedAt (frame : Locals) (status time root : UInt64) (boundary : Vector) : Prop where
  params : frame.params.length = 18
  locals : frame.locals.length = 157
  values : frame.values = []
  fuel : ∃ value : UInt64, frame.params[0]? = some (.i64 value)
  status : frame.locals[1]? = some (.i64 status)
  outputTime : frame.locals[2]? = some (.i64 time)
  outputOwner : frame.locals[3]? = some (.i64 root)
  outputPointer : frame.locals[4]? = some (.i64 root)
  boundary : ∀ i : Fin 12, frame.locals[5 + i.val]? = (vectorValues boundary).reverse[i.val]?
  done : frame.locals[17]? = some (.i64 1)

theorem AdvanceFrameAt.return_status {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary) (status : UInt64) :
    AdvanceReturnedAt (advanceReturnedFrame frame status time source boundary) status time source boundary := by
  constructor <;> simp_all [advanceReturnedFrame, h.params, h.locals,
    advanceParams, vectorValues, boundsValues]
  intro i
  fin_cases i <;> simp [h.locals]

theorem AdvanceReturnedAt.measure {frame : Locals} {status time root : UInt64} {boundary : Vector}
    (h : AdvanceReturnedAt frame status time root boundary) : advanceMeasure frame = 0 := by
  simp [advanceMeasure, h.done]

theorem advance_returned_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status time root : UInt64) (boundary : Vector) (h : AdvanceReturnedAt frame status time root boundary)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp module (advanceLoop.take 7 ++ rest) Q store frame env := by
  obtain ⟨fuel, hFuel⟩ := h.fuel
  have hShape := AnnotationMatches.function_184_while_loop_0_guard_eq
  change some (advanceLoop.take 7) = some (FuelGuard.program 0 35) at hShape
  rw [Option.some.inj hShape]
  apply FuelGuard.program_spec 0 35 module env store frame fuel 1 h.values
    (by simpa [Locals.get, h.params] using hFuel)
    (by simpa [Locals.get, h.params, h.locals] using h.done)
  simpa using hNext

def advanceReturnTail : Wasm.Program :=
  [.localSet 19, .localGet 3, .localSet 20, .localGet 4, .localSet 21,
    .localGet 5, .localSet 22] ++
    (List.range 12).flatMap (fun i => [.localGet (6 + i), .localSet (23 + i)]) ++
    [.constI64 1, .localSet 35]

theorem advance_scan_failure_shape :
    advanceScanFailureBody = [.constI64 2] ++ advanceReturnTail := rfl

theorem advance_trial_failure_shape :
    advanceTrialFailureBody = [.localGet 72] ++ advanceReturnTail := rfl

theorem advance_return_tail_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source status : UInt64) (boundary : Vector)
    (hParams : frame.params = advanceParams fuel n trials time source boundary)
    (hLocals : frame.locals.length = 157) (hValues : frame.values = [.i64 status])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (advanceReturnedFrame frame status time source boundary) env) :
    wp module (advanceReturnTail ++ rest) Q store frame env := by
  unfold advanceReturnTail
  simp only [List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append]
  certificate_advance_guard_peel
  simpa [advanceReturnedFrame, hParams, advanceParams, vectorValues, boundsValues] using hNext

#print axioms AdvanceFrameAt.return_status
#print axioms AdvanceReturnedAt.measure
#print axioms advance_returned_guard_spec
#print axioms advance_scan_failure_shape
#print axioms advance_trial_failure_shape
#print axioms advance_return_tail_spec
end Project.EulerCertificate.Execution
