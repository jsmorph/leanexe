import Project.EulerRiemann.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.EulerRiemann.AnnotationMatches

def function_25_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerRiemann.func25 [] 0 30).getD []

theorem function_25_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func25 [] 0 30 = some function_25_array_fold_0_program := by
  rfl

theorem function_25_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func25 []).getD []).drop 0 =
      Project.EulerRiemann.AnnotationMatches.function_25_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func25 []).getD []).drop 30 := by
  rfl









def function_74_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 11

theorem function_74_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func74
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_74_while_loop_0_guard_program := by
  rfl

theorem function_74_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerRiemann.func74 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_74_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func74 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_78_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 10

theorem function_78_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func78
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_78_while_loop_0_guard_program := by
  rfl

theorem function_78_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerRiemann.func78 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_78_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func78 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_88_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 8

theorem function_88_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerRiemann.func88
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_88_while_loop_0_guard_program := by
  rfl

theorem function_88_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerRiemann.func88 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_88_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerRiemann.func88 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.EulerRiemann.AnnotationMatches
