import LeanExeGen.GeneratedR23fa7efc3fb0298b.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64

import Project.ProofKit.GuardedBackEdge



import Project.ProofKit.FixedArrayCapacity

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

def function_0_array_fold_0_condition : Project.ProofKit.ScalarTransition.Expr .bool :=
  .ne (.get 16) (.const (0 : UInt64))

def function_0_array_fold_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .seq (.seq (.seq (.seq (.assign 3 (.bin .add (.get 1) (.get 2))) (.assign 17 (.get 3))) (.assign 16 (.const (0 : UInt64)))) (.assign 1 (.get 17))) (.assign 18 (.const (1 : UInt64)))

def function_0_array_fold_0_step_continuing : Project.ProofKit.ScalarTransition.Stmt :=
  .assign 13
    (.bin .add (.get 13) (.const 1))

def function_0_array_fold_0_step_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.guardedBackEdgeProgram
    11 function_0_array_fold_0_body function_0_array_fold_0_condition
    function_0_array_fold_0_step_continuing

theorem function_0_array_fold_0_step_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 62, field := .block }, { instructionIndex := 0, field := .loop }] 16
      37 = some function_0_array_fold_0_step_program := by
  rfl

def function_0_array_fold_0_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.resultProgram
    1 10

theorem function_0_array_fold_0_result_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .thenBranch }] 63
      65 = some function_0_array_fold_0_result_program := by
  rfl

def function_0_array_fold_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0], locals := [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20] }

def function_0_array_fold_0_conditionTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  some (((v16) != ((0 : UInt64))), function_0_array_fold_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20))

def function_0_array_fold_0_bodyTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  some (function_0_array_fold_0_state (v0) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v1) (v2)) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v1) (v2)) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) ((0 : UInt64)) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v1) (v2)) ((1 : UInt64)) (v19) (v20))

set_option linter.unusedSimpArgs false in
theorem function_0_array_fold_0_condition_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_0_array_fold_0_condition.evalU64 11
      (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) = function_0_array_fold_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
  simp (config := { maxSteps := 1000000 }) only [function_0_array_fold_0_condition, function_0_array_fold_0_state, function_0_array_fold_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false]

set_option linter.unusedSimpArgs false in
theorem function_0_array_fold_0_body_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_0_array_fold_0_body.evalU64 11
      (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) = function_0_array_fold_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
  simp (config := { maxSteps := 1000000 }) only [function_0_array_fold_0_body, function_0_array_fold_0_state, function_0_array_fold_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false]

theorem function_0_array_fold_0_condition_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_0_array_fold_0_condition.eval 11
      (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState =
        (function_0_array_fold_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).map fun result =>
          (result.1, result.2.toState) := by
  rw [Project.ProofKit.ScalarTransition.Expr.eval_toState,
    function_0_array_fold_0_condition_evalU64]

theorem function_0_array_fold_0_body_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_0_array_fold_0_body.eval 11
      (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState =
        (function_0_array_fold_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    function_0_array_fold_0_body_evalU64]

def function_0_length_dispatch_0_valid_capacity_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    1 1 11

theorem function_0_length_dispatch_0_valid_capacity_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .thenBranch }] 0
      18 = some function_0_length_dispatch_0_valid_capacity_program := by
  rfl

def function_0_length_dispatch_0_invalid_capacity_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    0 1 11

theorem function_0_length_dispatch_0_invalid_capacity_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedR23fa7efc3fb0298b.func0
      [{ instructionIndex := 7, field := .elseBranch }] 0
      18 = some function_0_length_dispatch_0_invalid_capacity_program := by
  rfl

end LeanExeGen.GeneratedR23fa7efc3fb0298b.AnnotationMatches
