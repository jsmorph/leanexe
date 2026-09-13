import Project.EulerRiemann.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.EulerRiemann.AnnotationMatches

def function_32_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerRiemann.func32 [] 0 30).getD []

theorem function_32_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func32 [] 0 30 = some function_32_array_fold_0_program := by
  rfl

theorem function_32_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func32 []).getD []).drop 0 =
      Project.EulerRiemann.AnnotationMatches.function_32_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func32 []).getD []).drop 30 := by
  rfl









def function_81_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 11

theorem function_81_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func81
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_81_while_loop_0_guard_program := by
  rfl

theorem function_81_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerRiemann.func81 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_81_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func81 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_85_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 10

theorem function_85_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func85
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_85_while_loop_0_guard_program := by
  rfl

theorem function_85_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerRiemann.func85 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_85_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func85 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_95_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 8

theorem function_95_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func95
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_95_while_loop_0_guard_program := by
  rfl

theorem function_95_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerRiemann.func95 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_95_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func95 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.EulerRiemann.AnnotationMatches
