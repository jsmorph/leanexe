import Project.EulerRiemann.InitialExtractCopy
import Project.EulerRiemann.AnnotationMatches
import Project.ProofKit.FuelGuard
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialLoop : Wasm.Program :=
  (Annotation.resolve func95
    [{ instructionIndex := 4, field := .block },
     { instructionIndex := 0, field := .loop }]).getD []

theorem initial_loop_shape : func95 = func95.take 4 ++
    [.block 0 0 [.loop 0 0 initialLoop]] ++ func95.drop 5 := rfl

theorem initial_loop_body_shape : initialLoop = initialLoop.take 7 ++
    (initialLoop.drop 7).take 7 ++ [.iff 0 0 initialDoneBody initialGrowBody, .br 0] := rfl

structure InitialFrameAt (frame : Locals) (fuel : UInt64) (n size : Nat)
    (source tracker output : UInt64) (done : Bool) : Prop where
  params : frame.params = [.i64 fuel, .i64 (UInt64.ofNat n), .i64 (UInt64.ofNat size),
    .i64 source, .i64 source]
  locals : frame.locals.length = 61
  values : frame.values = []
  tracker : frame.locals[0]? = some (.i64 tracker)
  outputOwner : frame.locals[1]? = some (.i64 output)
  outputPointer : frame.locals[2]? = some (.i64 output)
  done : frame.locals[3]? = some (.i64 (if done then 1 else 0))

def initialSelectedFrame (frame : Locals) (source : UInt64) : Locals :=
  resultFrame frame 48 source

def initialReturnedFrame (frame : Locals) (root : UInt64) : Locals :=
  resultFrame (resultFrame (resultFrame frame 6 root) 7 root) 8 1

theorem InitialFrameAt.selected {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done) :
    InitialFrameAt (initialSelectedFrame frame source) fuel n size source tracker output done := by
  cases h
  constructor <;> simp_all [initialSelectedFrame, resultFrame]

theorem InitialFrameAt.returned {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done) (root : UInt64) :
    InitialFrameAt (initialReturnedFrame frame root) fuel n size source tracker root true := by
  cases h
  constructor <;> simp_all [initialReturnedFrame, resultFrame]

def initialMeasure (frame : Locals) : Nat :=
  if frame.locals[3]? = some (.i64 1) then 0
  else match (frame.params[0]? : Option Wasm.Value) with
    | some (.i64 fuel) => fuel.toNat + 1 | _ => 0

theorem InitialFrameAt.measure {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done) :
    initialMeasure frame = if done then 0 else fuel.toNat + 1 := by
  cases done <;> simp [initialMeasure, h.done, h.params]

#print axioms initial_loop_shape
#print axioms initial_loop_body_shape
#print axioms InitialFrameAt.selected
#print axioms InitialFrameAt.returned
#print axioms InitialFrameAt.measure

end Project.EulerRiemann.Execution
