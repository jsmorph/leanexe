import Project.EulerReconstructed.TimeTransfers
import Project.EulerReconstructed.RetryFailureExecute
import Project.ProofKit.ScalarTransitionU64

namespace Project.EulerReconstructed.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult
open Project.EulerRiemann.Execution (boolWord)

structure RetryFrameAt (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time dt alpha source outputDt outputRoot : UInt64) (done : Bool) : Prop where
  params : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time,
    .i64 dt, .i64 alpha, .i64 source, .i64 source]
  locals : frame.locals.length = 77
  values : frame.values = []
  tracker : frame.locals[0]? = some (.i64 0)
  status : frame.locals[1]? = some (.i64 0)
  outputDt : frame.locals[2]? = some (.i64 outputDt)
  outputOwner : frame.locals[3]? = some (.i64 outputRoot)
  outputPointer : frame.locals[4]? = some (.i64 outputRoot)
  done : frame.locals[5]? = some (.i64 (boolWord done))

def retryGuardFrame (frame : Locals) (time dt : UInt64) (valid : Bool) : Locals :=
  let locals := frame.locals.set 6 (.i64 time)
  let locals := locals.set 7 (.i64 dt)
  let locals := locals.set 8 (.i64 (boolWord valid))
  { frame with locals, values := [] }

theorem RetryFrameAt.guard {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done) (valid : Bool) :
    RetryFrameAt (retryGuardFrame frame time dt valid)
      fuel n trials time dt alpha source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryGuardFrame]

def retryMeasure (frame : Locals) : Nat :=
  if frame.locals[5]? = some (.i64 1) then 0
  else match (frame.params[0]? : Option Wasm.Value) with
    | some (.i64 fuel) => fuel.toNat + 1 | _ => 0

theorem RetryFrameAt.measure {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot done) :
    retryMeasure frame = if done then 0 else fuel.toNat + 1 := by
  cases done <;> simp [retryMeasure, h.done, h.params, boolWord]

def RetryScratch (frame : Locals) : Prop :=
  frame.locals.drop 71 = List.replicate 6 (.i64 0)

theorem RetryScratch.guard {frame : Locals} (h : RetryScratch frame)
    (time dt : UInt64) (valid : Bool) : RetryScratch (retryGuardFrame frame time dt valid) := by
  unfold RetryScratch retryGuardFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem RetryScratch.frame_eq {frame : Locals} (h : RetryScratch frame) (hValues : frame.values = []) :
    frame = FixedArraySearch.frame frame.params (frame.locals.take 71) [] 0 0 0 0 0 0 := by
  apply Frame.ext
  · rfl
  · change frame.locals = frame.locals.take 71 ++ List.replicate 6 (.i64 0)
    rw [← h]
    exact (List.take_append_drop 71 frame.locals).symm
  · exact hValues

structure RetryReturnedAt (frame : Locals) (status dt root : UInt64) : Prop where
  params : frame.params.length = 8
  locals : frame.locals.length = 77
  values : frame.values = []
  fuel : ∃ value : UInt64, frame.params[0]? = some (.i64 value)
  status : frame.locals[1]? = some (.i64 status)
  outputDt : frame.locals[2]? = some (.i64 dt)
  outputOwner : frame.locals[3]? = some (.i64 root)
  outputPointer : frame.locals[4]? = some (.i64 root)
  done : frame.locals[5]? = some (.i64 1)

theorem RetryFrameAt.returned {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time dt alpha source outputDt outputRoot : UInt64}
    (h : RetryFrameAt frame fuel n trials time dt alpha source outputDt outputRoot true) :
    RetryReturnedAt frame 0 outputDt outputRoot := by
  exact ⟨by simp [h.params], h.locals, h.values, ⟨fuel, by simp [h.params]⟩,
    h.status, h.outputDt, h.outputOwner, h.outputPointer, h.done⟩

theorem retry_failure_returned (params saved : List Wasm.Value)
    (hParams : params.length = 8) (hSaved : saved.length = 71)
    (hFuel : ∃ value : UInt64, params[0]? = some (.i64 value))
    (status dt previous current capacity next root : UInt64) :
    RetryReturnedAt (resultFrame (retryFailureFrame params saved status dt previous current capacity next root)
      13 1) status dt root := by
  constructor <;>
    simp_all [resultFrame, retryFailureFrame, finishFrame, FixedArraySearch.frame,
      retryFailureSaved]

theorem RetryReturnedAt.measure {frame : Locals} {status dt root : UInt64}
    (h : RetryReturnedAt frame status dt root) : retryMeasure frame = 0 := by
  simp [retryMeasure, h.done]

#print axioms RetryFrameAt.guard
#print axioms RetryFrameAt.measure
#print axioms RetryScratch.guard
#print axioms RetryScratch.frame_eq
#print axioms RetryFrameAt.returned
#print axioms retry_failure_returned
#print axioms RetryReturnedAt.measure
end Project.EulerReconstructed.Execution
