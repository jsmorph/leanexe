import Project.EulerRiemann.RetryBranches
import Project.ProofKit.ScalarTransitionU64

namespace Project.EulerRiemann.Execution
open Wasm

structure RetryFrameAt (frame : Locals) (fuel : UInt64) (n : Nat)
    (time dt source outputDt outputRoot : UInt64) (done : Bool) : Prop where
  params : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time,
    .i64 dt, .i64 source, .i64 source]
  locals : frame.locals.length = 51
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
    {time dt source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot done) (valid : Bool) :
    RetryFrameAt (retryGuardFrame frame time dt valid)
      fuel n time dt source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryGuardFrame]

theorem RetryFrameAt.trial {frame : Locals} {fuel : UInt64} {n : Nat}
    {time dt source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot done)
    (ratio result : UInt64) (accepted : Bool) :
    RetryFrameAt (retryTrialFrame frame n ratio source result accepted)
      fuel n time dt source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryTrialFrame]

theorem RetryFrameAt.accept {frame : Locals} {fuel : UInt64} {n : Nat}
    {time dt source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot done) (result : UInt64) :
    RetryFrameAt (retryAcceptedFrame frame dt result) fuel n time dt source dt result true := by
  cases h
  constructor <;> simp_all [retryAcceptedFrame, boolWord]

theorem RetryFrameAt.reject {frame : Locals} {fuel : UInt64} {n : Nat}
    {time dt source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot done) (frees : UInt64) :
    RetryFrameAt (retryRejectedFrame frame fuel n time dt source frees)
      (fuel - 1) n time (IEEE64.mul 0x3FE0000000000000 dt) source outputDt outputRoot done := by
  cases h
  constructor <;> simp_all [retryRejectedFrame]

def retryMeasure (frame : Locals) : Nat :=
  if frame.locals[5]? = some (.i64 1) then 0
  else match (frame.params[0]? : Option Wasm.Value) with
    | some (.i64 fuel) => fuel.toNat + 1 | _ => 0

theorem RetryFrameAt.measure {frame : Locals} {fuel : UInt64} {n : Nat}
    {time dt source outputDt outputRoot : UInt64} {done : Bool}
    (h : RetryFrameAt frame fuel n time dt source outputDt outputRoot done) :
    retryMeasure frame = if done then 0 else fuel.toNat + 1 := by
  cases done <;> simp [retryMeasure, h.done, h.params, boolWord]

theorem retryFuel_decreases (fuel : UInt64) (hFuel : fuel ≠ 0) :
    (fuel - 1).toNat + 1 < fuel.toNat + 1 := by
  exact Nat.add_lt_add_right
    (Project.ProofKit.ScalarTransition.CounterTransition.decrement_toNat_lt hFuel) 1

#print axioms RetryFrameAt.guard
#print axioms RetryFrameAt.trial
#print axioms RetryFrameAt.accept
#print axioms RetryFrameAt.reject
#print axioms RetryFrameAt.measure
#print axioms retryFuel_decreases

end Project.EulerRiemann.Execution
