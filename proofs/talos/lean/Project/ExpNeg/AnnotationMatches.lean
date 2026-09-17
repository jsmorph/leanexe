import Project.ExpNeg.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.ExpNeg.AnnotationMatches

def function_1_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 5

theorem function_1_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.ExpNeg.func1
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_1_while_loop_0_guard_program := by
  rfl

theorem function_1_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.ExpNeg.func1 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_1_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.ExpNeg.func1 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_2_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 3

theorem function_2_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.ExpNeg.func2
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_2_while_loop_0_guard_program := by
  rfl

theorem function_2_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.ExpNeg.func2 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_2_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.ExpNeg.func2 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.ExpNeg.AnnotationMatches
