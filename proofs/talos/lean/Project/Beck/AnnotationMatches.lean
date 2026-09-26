import Project.Beck.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.Beck.AnnotationMatches

def function_18_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 12

theorem function_18_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func18
      [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_18_while_loop_0_guard_program := by
  rfl

theorem function_18_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func18 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_18_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func18 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_20_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 17

theorem function_20_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func20
      [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_20_while_loop_0_guard_program := by
  rfl

theorem function_20_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func20 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_20_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func20 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_25_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 15

theorem function_25_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func25
      [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_25_while_loop_0_guard_program := by
  rfl

theorem function_25_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func25 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_25_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func25 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.Beck.AnnotationMatches
