import Project.Beck.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard



import Project.ProofKit.FixedArrayCopy












set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.Beck.AnnotationMatches

def function_17_erase_copy_0_prefix_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.prefixProgram
    8 14
    11 15

def function_17_erase_copy_0_suffix_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.suffixProgram
    1 8 14
    11 12
    15

def function_17_erase_copy_0_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCopy.program
    1 8 14
    11 12
    15

theorem function_17_erase_copy_0_prefix_eq :
    Project.ProofKit.Annotation.region Project.Beck.func17
      [{ instructionIndex := 15, field := .thenBranch }] 53
      56 = some function_17_erase_copy_0_prefix_program := by
  rfl

theorem function_17_erase_copy_0_suffix_eq :
    Project.ProofKit.Annotation.region Project.Beck.func17
      [{ instructionIndex := 15, field := .thenBranch }] 56
      59 = some function_17_erase_copy_0_suffix_program := by
  rfl

theorem function_17_erase_copy_0_eq :
    Project.ProofKit.Annotation.region Project.Beck.func17
      [{ instructionIndex := 15, field := .thenBranch }] 53
      59 = some function_17_erase_copy_0_program := by
  rfl

theorem function_17_erase_copy_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.Beck.func17 [{ instructionIndex := 15, field := .thenBranch }]).getD []).drop 53 =
      Project.Beck.AnnotationMatches.function_17_erase_copy_0_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func17 [{ instructionIndex := 15, field := .thenBranch }]).getD []).drop 59 := by
  rfl

def function_18_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 12

theorem function_18_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func18
      [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_18_while_loop_0_guard_program := by
  rfl

theorem function_18_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func18 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_18_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func18 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_21_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 17

theorem function_21_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func21
      [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_21_while_loop_0_guard_program := by
  rfl

theorem function_21_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func21 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_21_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func21 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_26_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 15

theorem function_26_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func26
      [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_26_while_loop_0_guard_program := by
  rfl

theorem function_26_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func26 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_26_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func26 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.Beck.AnnotationMatches
