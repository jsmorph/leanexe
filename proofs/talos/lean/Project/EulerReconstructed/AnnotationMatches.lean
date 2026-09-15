import Project.EulerReconstructed.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.EulerReconstructed.AnnotationMatches

def function_46_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerReconstructed.func46 [] 0 30).getD []

theorem function_46_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerReconstructed.func46 [] 0 30 = some function_46_array_fold_0_program := by
  rfl

theorem function_46_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func46 []).getD []).drop 0 =
      Project.EulerReconstructed.AnnotationMatches.function_46_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func46 []).getD []).drop 30 := by
  rfl









def function_73_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 20

theorem function_73_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerReconstructed.func73
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_73_while_loop_0_guard_program := by
  rfl

theorem function_73_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func73 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_73_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func73 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_125_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 13

theorem function_125_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerReconstructed.func125
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_125_while_loop_0_guard_program := by
  rfl

theorem function_125_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func125 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_125_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func125 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_129_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 11

theorem function_129_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerReconstructed.func129
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_129_while_loop_0_guard_program := by
  rfl

theorem function_129_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func129 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_129_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func129 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_140_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 8

theorem function_140_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerReconstructed.func140
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_140_while_loop_0_guard_program := by
  rfl

theorem function_140_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func140 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_140_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerReconstructed.func140 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.EulerReconstructed.AnnotationMatches
