import Project.EulerReconstruction.Candidate
import Project.ProofKit.BlockLoop
import Project.ProofKit.ScalarTransitionU64

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction
open Project.EulerConservative.Execution (boolWord)

def limitLoop : Wasm.Program :=
  (Project.ProofKit.Annotation.resolve func38
    [{ instructionIndex := 2, field := .block },
     { instructionIndex := 0, field := .loop }]).getD []

theorem limit_loop_shape : func38 = func38.take 2 ++
    [.block 0 0 [.loop 0 0 limitLoop]] ++ func38.drop 3 := rfl

theorem limit_guard_shape : limitLoop = Project.ProofKit.FuelGuard.program 0 20 ++
    limitLoop.drop 7 :=
  Project.EulerReconstruction.AnnotationMatches.function_38_while_loop_0_guard_tail_eq

def limitParams (fuel : UInt64) (center delta : State) (factor : UInt64) : List Value :=
  [.i64 fuel, .i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy,
    .i64 delta.density, .i64 delta.mx, .i64 delta.my, .i64 delta.energy, .i64 factor]

structure LimitFrameAt (frame : Locals) (fuel : UInt64) (center delta : State)
    (factor : UInt64) (output : Faces) (done : Bool) : Prop where
  params : frame.params = limitParams fuel center delta factor
  locals : frame.locals.length = 72
  values : frame.values = []
  status : frame.locals[0]? = some (.i64 output.status)
  leftDensity : frame.locals[1]? = some (.i64 output.left.density)
  leftMx : frame.locals[2]? = some (.i64 output.left.mx)
  leftMy : frame.locals[3]? = some (.i64 output.left.my)
  leftEnergy : frame.locals[4]? = some (.i64 output.left.energy)
  rightDensity : frame.locals[5]? = some (.i64 output.right.density)
  rightMx : frame.locals[6]? = some (.i64 output.right.mx)
  rightMy : frame.locals[7]? = some (.i64 output.right.my)
  rightEnergy : frame.locals[8]? = some (.i64 output.right.energy)
  factor : frame.locals[9]? = some (.i64 output.factor)
  done : frame.locals[10]? = some (.i64 (boolWord done))

def limitMeasure (frame : Locals) : Nat :=
  if frame.locals[10]? = some (.i64 1) then 0
  else match (frame.params[0]? : Option Value) with
    | some (.i64 fuel) => fuel.toNat + 1
    | _ => 0

theorem LimitFrameAt.measure {frame : Locals} {fuel : UInt64} {center delta : State}
    {factor : UInt64} {output : Faces} {done : Bool}
    (h : LimitFrameAt frame fuel center delta factor output done) :
    limitMeasure frame = if done then 0 else fuel.toNat + 1 := by
  cases done <;> simp [limitMeasure, h.done, h.params, limitParams, boolWord]

def limitInvariant (initial : Store Unit) (center delta : State) (expected : Faces)
    (store : Store Unit) (frame : Locals) : Prop :=
  store = initial ∧ ∃ fuel factor output done,
    LimitFrameAt frame fuel center delta factor output done ∧
    expected = if done then output else limit fuel.toNat center delta factor

def limitDone (initial : Store Unit) (center delta : State) (expected : Faces)
    (store : Store Unit) (frame : Locals) : Prop :=
  store = initial ∧ ∃ fuel factor output done,
    LimitFrameAt frame fuel center delta factor output done ∧
    (fuel = 0 ∨ done = true) ∧
    expected = if done then output else constantFaces center

#print axioms limit_loop_shape
#print axioms limit_guard_shape
#print axioms LimitFrameAt.measure

end Project.EulerReconstruction.Execution
