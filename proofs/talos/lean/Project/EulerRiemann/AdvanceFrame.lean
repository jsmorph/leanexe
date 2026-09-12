import Project.EulerRiemann.AdvanceLoopShape

namespace Project.EulerRiemann.Execution
open Wasm

structure AdvanceFrameAt (frame : Locals) (fuel : UInt64) (n : Nat)
    (time source tracker outputTime outputRoot : UInt64) (done : Bool) : Prop where
  params : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 time, .i64 source, .i64 source]
  locals : frame.locals.length = 45
  values : frame.values = []
  tracker : frame.locals[0]? = some (.i64 tracker)
  status : frame.locals[1]? = some (.i64 0)
  outputTime : frame.locals[2]? = some (.i64 outputTime)
  outputOwner : frame.locals[3]? = some (.i64 outputRoot)
  outputPointer : frame.locals[4]? = some (.i64 outputRoot)
  done : frame.locals[5]? = some (.i64 (boolWord done))

def advanceFinishedFrame (frame : Locals) (time source : UInt64) : Locals :=
  let locals := frame.locals.set 1 (.i64 0)
  let locals := locals.set 2 (.i64 time)
  let locals := locals.set 3 (.i64 source)
  let locals := locals.set 4 (.i64 source)
  let locals := locals.set 5 (.i64 1)
  { frame with locals, values := [] }

def advanceContinuedFrame (frame : Locals) (fuel : UInt64) (n : Nat)
    (nextTime result : UInt64) : Locals :=
  let locals := frame.locals.set 32 (.i64 (UInt64.ofNat n))
  let locals := locals.set 33 (.i64 nextTime)
  let locals := locals.set 34 (.i64 result)
  let locals := locals.set 35 (.i64 result)
  let locals := locals.set 36 (.i64 (UInt64.ofNat n))
  let locals := locals.set 37 (.i64 nextTime)
  let locals := locals.set 38 (.i64 result)
  let locals := locals.set 39 (.i64 result)
  let locals := locals.set 40 (.i64 result)
  let locals := locals.set 0 (.i64 result)
  { params := [.i64 (fuel - 1), .i64 (UInt64.ofNat n), .i64 nextTime, .i64 result, .i64 result]
    locals
    values := [] }

theorem AdvanceFrameAt.time {frame : Locals} {fuel : UInt64} {n : Nat}
    {time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done) :
    AdvanceFrameAt (advanceTimeFrame frame) fuel n time source tracker outputTime outputRoot done := by
  cases h
  constructor <;> simp_all [advanceTimeFrame]

theorem AdvanceFrameAt.scan {frame : Locals} {fuel : UInt64} {n : Nat}
    {time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done) (stats : Traversal.Scan) :
    AdvanceFrameAt (advanceScanFrame frame source stats)
      fuel n time source tracker outputTime outputRoot done := by
  cases h
  constructor <;> simp_all [advanceScanFrame]

theorem AdvanceFrameAt.trial {frame : Locals} {fuel : UInt64} {n : Nat}
    {time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done)
    (alpha dt trialDt result : UInt64) :
    AdvanceFrameAt (advanceTrialFrame frame n time source alpha dt trialDt result)
      fuel n time source tracker outputTime outputRoot done := by
  cases h
  constructor <;> simp_all [advanceTrialFrame]

theorem AdvanceFrameAt.finish {frame : Locals} {fuel : UInt64} {n : Nat}
    {time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done) :
    AdvanceFrameAt (advanceFinishedFrame frame time source) fuel n time source tracker time source true := by
  cases h
  constructor <;> simp_all [advanceFinishedFrame, boolWord]

theorem AdvanceFrameAt.continued {frame : Locals} {fuel : UInt64} {n : Nat}
    {time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done)
    (nextTime result : UInt64) :
    AdvanceFrameAt (advanceContinuedFrame frame fuel n nextTime result)
      (fuel - 1) n nextTime result result outputTime outputRoot done := by
  cases h
  constructor <;> simp_all [advanceContinuedFrame]

def advanceMeasure (frame : Locals) : Nat :=
  if frame.locals[5]? = some (.i64 1) then 0
  else match (frame.params[0]? : Option Wasm.Value) with
    | some (.i64 fuel) => fuel.toNat + 1 | _ => 0

theorem AdvanceFrameAt.measure {frame : Locals} {fuel : UInt64} {n : Nat}
    {time source tracker outputTime outputRoot : UInt64} {done : Bool}
    (h : AdvanceFrameAt frame fuel n time source tracker outputTime outputRoot done) :
    advanceMeasure frame = if done then 0 else fuel.toNat + 1 := by
  cases done <;> simp [advanceMeasure, h.done, h.params, boolWord]

#print axioms AdvanceFrameAt.time
#print axioms AdvanceFrameAt.scan
#print axioms AdvanceFrameAt.trial
#print axioms AdvanceFrameAt.finish
#print axioms AdvanceFrameAt.continued
#print axioms AdvanceFrameAt.measure

end Project.EulerRiemann.Execution
