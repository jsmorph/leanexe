import Project.Drone.Program
import Project.ProofKit.Annotation
import Project.ProofKit.WordArrayPushProgram

namespace Project.Drone.Execution
open Wasm Project.ProofKit

def advanceBody : Wasm.Program :=
  (Annotation.resolve func18
    [{ instructionIndex := 6, field := .block },
      { instructionIndex := 0, field := .loop }]).getD []

theorem advance_time_push_shape : (advanceBody.drop 49).take 67 =
    WordArrayPush.program 52 := rfl

theorem advance_excess_push_shape : (advanceBody.drop 121).take 67 =
    WordArrayPush.program 52 := rfl

theorem advance_parent_push_shape : (advanceBody.drop 193).take 67 =
    WordArrayPush.program 52 := rfl

#print axioms advance_time_push_shape
#print axioms advance_excess_push_shape
#print axioms advance_parent_push_shape
end Project.Drone.Execution
