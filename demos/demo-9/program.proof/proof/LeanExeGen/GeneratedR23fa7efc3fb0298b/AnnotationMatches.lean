import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult



import Project.ProofKit.FixedArrayTraversalInput

import Project.ProofKit.FixedArrayFold




set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches

def function_0_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0 [{ instructionIndex := 7, field := .thenBranch }] 39 65).getD []

theorem function_0_array_fold_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0 [{ instructionIndex := 7, field := .thenBranch }] 39 65 = some function_0_array_fold_0_program := by
  rfl

def function_0_array_fold_0_setup_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.forwardSetupProgram
    11 12
    13 16
    14 1
    18 15
    0

theorem function_0_array_fold_0_setup_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .thenBranch }] 39
      62 = some function_0_array_fold_0_setup_program := by
  rfl

def function_0_array_fold_0_continuing_program : Wasm.Program :=
  Project.ProofKit.FixedArrayTraversalInput.continuingProgram
    11 13
    15 2

theorem function_0_array_fold_0_continuing_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 62, field := .block }, { instructionIndex := 0, field := .loop }] 0 16 =
        some function_0_array_fold_0_continuing_program := by
  rfl

def function_0_array_fold_0_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.resultProgram
    1 10

theorem function_0_array_fold_0_result_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .thenBranch }] 63
      65 = some function_0_array_fold_0_result_program := by
  rfl

end LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
