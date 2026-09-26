import Project.EulerReconstructed.FrozenAdvanceGuard

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm Project.ProofKit

structure AdvanceReturnedAt (frame : Locals) (status time root : UInt64) : Prop where
  params : frame.params.length = 6
  locals : frame.locals.length = 49
  values : frame.values = []
  fuel : ∃ value : UInt64, frame.params[0]? = some (.i64 value)
  status : frame.locals[1]? = some (.i64 status)
  outputTime : frame.locals[2]? = some (.i64 time)
  outputOwner : frame.locals[3]? = some (.i64 root)
  outputPointer : frame.locals[4]? = some (.i64 root)
  done : frame.locals[5]? = some (.i64 1)

def advanceReturnedFrame (frame : Locals) (status time source : UInt64) : Locals :=
  let locals := frame.locals.set 1 (.i64 status)
  let locals := locals.set 2 (.i64 time)
  let locals := locals.set 3 (.i64 source)
  let locals := locals.set 4 (.i64 source)
  let locals := locals.set 5 (.i64 1)
  { frame with locals, values := [] }

theorem AdvanceFrameAt.returned {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot true) :
    AdvanceReturnedAt frame 0 outputTime outputRoot :=
  ⟨by simp [h.params], h.locals, h.values, ⟨fuel, by simp [h.params]⟩,
    h.status, h.outputTime, h.outputOwner, h.outputPointer, h.done⟩

theorem AdvanceFrameAt.return_status {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done) (status : UInt64) :
    AdvanceReturnedAt (advanceReturnedFrame frame status time source) status time source := by
  constructor <;> simp_all [advanceReturnedFrame, advanceFinishedFrame, h.params, h.locals, h.values]

theorem AdvanceReturnedAt.measure {frame : Locals} {status time root : UInt64}
    (h : AdvanceReturnedAt frame status time root) : advanceMeasure frame = 0 := by
  simp [advanceMeasure, h.done]

theorem advance_returned_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status time root : UInt64) (h : AdvanceReturnedAt frame status time root)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp module (advanceLoop.take 7 ++ rest) Q store frame env := by
  obtain ⟨fuel, hFuel⟩ := h.fuel
  have hShape := AnnotationMatches.function_129_while_loop_0_guard_eq
  change some (advanceLoop.take 7) = some (FuelGuard.program 0 11) at hShape
  rw [Option.some.inj hShape]
  apply FuelGuard.program_spec 0 11 module env store frame fuel 1 h.values
    (by simpa [Locals.get, h.params] using hFuel)
    (by simpa [Locals.get, h.params, h.locals] using h.done)
  simpa using hNext

def advanceReturnTail : Wasm.Program :=
  [.localSet 7, .localGet 3, .localSet 8, .localGet 4, .localSet 9,
    .localGet 5, .localSet 10, .constI64 1, .localSet 11]

theorem advance_scan_failure_shape :
    advanceScanFailureBody = [.constI64 2] ++ advanceReturnTail := rfl

theorem advance_trial_failure_shape :
    advanceTrialFailureBody = [.localGet 36] ++ advanceReturnTail := rfl

theorem advance_return_tail_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel : UInt64) (n : Nat) (trials time source status : UInt64)
    (hParams : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time, .i64 source, .i64 source])
    (hLocals : frame.locals.length = 49) (hValues : frame.values = [.i64 status])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store (advanceReturnedFrame frame status time source) env) :
    wp module (advanceReturnTail ++ rest) Q store frame env := by
  unfold advanceReturnTail
  reconstructed_advance_guard_peel
  simpa [advanceReturnedFrame, advanceFinishedFrame, hParams] using hNext

#print axioms AdvanceFrameAt.returned
#print axioms AdvanceFrameAt.return_status
#print axioms AdvanceReturnedAt.measure
#print axioms advance_returned_guard_spec
#print axioms advance_scan_failure_shape
#print axioms advance_trial_failure_shape
#print axioms advance_return_tail_spec

end Project.EulerReconstructed.Frozen.Execution
