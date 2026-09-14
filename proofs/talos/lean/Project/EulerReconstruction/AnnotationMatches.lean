import Project.EulerReconstruction.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.EulerReconstruction.AnnotationMatches

def function_38_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 20

theorem function_38_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerReconstruction.func38
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_38_while_loop_0_guard_program := by
  rfl

theorem function_38_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerReconstruction.func38 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_38_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerReconstruction.func38 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.EulerReconstruction.AnnotationMatches
