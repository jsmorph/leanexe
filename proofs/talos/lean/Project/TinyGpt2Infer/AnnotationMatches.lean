import Project.TinyGpt2Infer.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.TinyGpt2Infer.AnnotationMatches

def function_35_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 5

theorem function_35_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.TinyGpt2Infer.func35
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_35_while_loop_0_guard_program := by
  rfl

theorem function_35_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.TinyGpt2Infer.func35 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_35_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.TinyGpt2Infer.func35 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_36_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 3

theorem function_36_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.TinyGpt2Infer.func36
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_36_while_loop_0_guard_program := by
  rfl

theorem function_36_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.TinyGpt2Infer.func36 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_36_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.TinyGpt2Infer.func36 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.TinyGpt2Infer.AnnotationMatches
