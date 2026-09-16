import Project.EulerCertificate.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.EulerCertificate.AnnotationMatches

def function_52_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 8

theorem function_52_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func52
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_52_while_loop_0_guard_program := by
  rfl

theorem function_52_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerCertificate.func52 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_52_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func52 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_74_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerCertificate.func74 [] 37 107).getD []

theorem function_74_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func74 [] 37 107 = some function_74_array_fold_0_program := by
  rfl

theorem function_74_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func74 []).getD []).drop 37 =
      Project.EulerCertificate.AnnotationMatches.function_74_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func74 []).getD []).drop 107 := by
  rfl









def function_89_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerCertificate.func89 [] 0 30).getD []

theorem function_89_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func89 [] 0 30 = some function_89_array_fold_0_program := by
  rfl

theorem function_89_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func89 []).getD []).drop 0 =
      Project.EulerCertificate.AnnotationMatches.function_89_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func89 []).getD []).drop 30 := by
  rfl









def function_114_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 20

theorem function_114_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func114
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_114_while_loop_0_guard_program := by
  rfl

theorem function_114_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerCertificate.func114 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_114_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func114 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_173_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerCertificate.func173 [] 37 103).getD []

theorem function_173_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func173 [] 37 103 = some function_173_array_fold_0_program := by
  rfl

theorem function_173_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func173 []).getD []).drop 37 =
      Project.EulerCertificate.AnnotationMatches.function_173_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func173 []).getD []).drop 103 := by
  rfl









def function_179_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 25

theorem function_179_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func179
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_179_while_loop_0_guard_program := by
  rfl

theorem function_179_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerCertificate.func179 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_179_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func179 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_184_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 35

theorem function_184_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.EulerCertificate.func184
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_184_while_loop_0_guard_program := by
  rfl

theorem function_184_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.EulerCertificate.func184 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_184_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerCertificate.func184 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.EulerCertificate.AnnotationMatches
