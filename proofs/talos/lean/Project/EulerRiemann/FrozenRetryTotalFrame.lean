import Project.EulerRiemann.FrozenRetryFailureExecute
import Project.EulerRiemann.FrozenRetryGuard

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult

def RetryScratch (frame : Locals) : Prop :=
  frame.locals.drop 45 = List.replicate 6 (.i64 0)

theorem RetryScratch.guard {frame : Locals} (h : RetryScratch frame)
    (time dt : UInt64) (valid : Bool) : RetryScratch (retryGuardFrame frame time dt valid) := by
  unfold RetryScratch retryGuardFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem RetryScratch.trial {frame : Locals} (h : RetryScratch frame)
    (n : Nat) (ratio source result : UInt64) (accepted : Bool) :
    RetryScratch (retryTrialFrame frame n ratio source result accepted) := by
  unfold RetryScratch retryTrialFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem RetryScratch.reject {frame : Locals} (h : RetryScratch frame)
    (fuel : UInt64) (n : Nat) (time dt source frees : UInt64) :
    RetryScratch (retryRejectedFrame frame fuel n time dt source frees) := by
  unfold RetryScratch retryRejectedFrame
  dsimp only
  repeat rw [List.drop_set_of_lt (by decide)]
  exact h

theorem RetryScratch.frame_eq {frame : Locals} (h : RetryScratch frame) (hValues : frame.values = []) :
    frame = FixedArraySearch.frame frame.params (frame.locals.take 45) [] 0 0 0 0 0 0 := by
  apply Frame.ext
  · rfl
  · change frame.locals = frame.locals.take 45 ++ List.replicate 6 (.i64 0)
    rw [← h]
    exact (List.take_append_drop 45 frame.locals).symm
  · exact hValues

structure RetryReturnedAt (frame : Locals) (status dt root : UInt64) : Prop where
  params : frame.params.length = 6
  locals : frame.locals.length = 51
  values : frame.values = []
  fuel : ∃ value : UInt64, frame.params[0]? = some (.i64 value)
  status : frame.locals[1]? = some (.i64 status)
  outputDt : frame.locals[2]? = some (.i64 dt)
  outputOwner : frame.locals[3]? = some (.i64 root)
  outputPointer : frame.locals[4]? = some (.i64 root)
  done : frame.locals[5]? = some (.i64 1)

theorem RetryFrameAt.returned {frame : Locals} {fuel : UInt64} {n : Nat}
    {time dt source outputDt outputRoot : UInt64}
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot true) :
    RetryReturnedAt frame 0 outputDt outputRoot := by
  exact ⟨by simp [h.params], h.locals, h.values, ⟨fuel, by simp [h.params]⟩,
    h.status, h.outputDt, h.outputOwner, h.outputPointer, h.done⟩

theorem retry_failure_returned (params saved : List Wasm.Value)
    (hParams : params.length = 6) (hSaved : saved.length = 45)
    (hFuel : ∃ value : UInt64, params[0]? = some (.i64 value))
    (status dt previous current capacity next root : UInt64) :
    RetryReturnedAt (resultFrame (retryFailureFrame params saved status dt previous current capacity next root)
      11 1) status dt root := by
  constructor <;>
    simp_all [resultFrame, retryFailureFrame, finishFrame, FixedArraySearch.frame,
      retryFailureSaved]

theorem RetryReturnedAt.measure {frame : Locals} {status dt root : UInt64}
    (h : RetryReturnedAt frame status dt root) : retryMeasure frame = 0 := by
  simp [retryMeasure, h.done]

theorem retry_returned_guard_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (status dt root : UInt64) (h : RetryReturnedAt frame status dt root)
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : Q (.Break 1 store frame)) :
    wp module (retryLoop.take 7 ++ rest) Q store frame env := by
  obtain ⟨fuel, hFuel⟩ := h.fuel
  have hShape := AnnotationMatches.function_81_while_loop_0_guard_eq
  change some (retryLoop.take 7) = some (FuelGuard.program 0 11) at hShape
  rw [Option.some.inj hShape]
  apply FuelGuard.program_spec 0 11 module env store frame fuel 1 h.values
    (by simpa [Locals.get, h.params] using hFuel)
    (by simpa [Locals.get, h.params, h.locals] using h.done)
  simpa using hNext

#print axioms RetryScratch.guard
#print axioms RetryScratch.trial
#print axioms RetryScratch.reject
#print axioms RetryScratch.frame_eq
#print axioms RetryFrameAt.returned
#print axioms retry_failure_returned
#print axioms RetryReturnedAt.measure
#print axioms retry_returned_guard_spec

end Project.EulerRiemann.Frozen.Execution
