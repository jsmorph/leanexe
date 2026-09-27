import LeanExeGen.GeneratedRa8e90ffc5781d113.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64

import Project.ProofKit.GuardedBackEdge



import Project.ProofKit.FixedArrayLengthDispatch

import Project.ProofKit.FixedArrayCapacity

import Project.ProofKit.FixedArrayTraversalInput

import Project.ProofKit.FixedArrayFold




set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches

def function_0_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0 [{ instructionIndex := 7, field := .thenBranch }] 39 65).getD []

theorem function_0_array_fold_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0 [{ instructionIndex := 7, field := .thenBranch }] 39 65 = some function_0_array_fold_0_program := by
  rfl

def function_0_array_fold_0_setup_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.forwardSetupProgram
    11 12
    13 16
    14 1
    18 15
    1

theorem function_0_array_fold_0_setup_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .thenBranch }] 39
      62 = some function_0_array_fold_0_setup_program := by
  rfl

def function_0_array_fold_0_continuing_program : Wasm.Program :=
  Project.ProofKit.FixedArrayTraversalInput.continuingProgram
    11 13
    15 2

theorem function_0_array_fold_0_continuing_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 62, field := .block }, { instructionIndex := 0, field := .loop }] 0 16 =
        some function_0_array_fold_0_continuing_program := by
  rfl

def function_0_array_fold_0_condition : Project.ProofKit.ScalarTransition.Expr .bool :=
  .ne (.get 16) (.const (0 : UInt64))

def function_0_array_fold_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .seq (.seq (.seq (.seq (.assign 3 (.bin .mul (.get 1) (.get 2))) (.assign 17 (.get 3))) (.assign 16 (.const (0 : UInt64)))) (.assign 1 (.get 17))) (.assign 18 (.const (1 : UInt64)))

def function_0_array_fold_0_step_continuing : Project.ProofKit.ScalarTransition.Stmt :=
  .assign 13 (.bin .add (.get 13) (.const (1 : UInt64)))

def function_0_array_fold_0_step_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.guardedBackEdgeProgram
    11 function_0_array_fold_0_body function_0_array_fold_0_condition
    function_0_array_fold_0_step_continuing

theorem function_0_array_fold_0_step_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .thenBranch }, { instructionIndex := 62, field := .block }, { instructionIndex := 0, field := .loop }] 16
      37 = some function_0_array_fold_0_step_program := by
  rfl

def function_0_array_fold_0_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.resultProgram
    1 10

theorem function_0_array_fold_0_result_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .thenBranch }] 63
      65 = some function_0_array_fold_0_result_program := by
  rfl

def function_0_array_fold_0_singleton_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.singletonResultProgram
    1 10
    7 4
    6

theorem function_0_array_fold_0_singleton_result_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .thenBranch }] 63
      81 = some
        function_0_array_fold_0_singleton_result_program := by
  rfl

def function_0_array_fold_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0], locals := [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20] }

def function_0_array_fold_0_conditionTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  some (((v16) != ((0 : UInt64))), function_0_array_fold_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20))

def function_0_array_fold_0_bodyTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  some (function_0_array_fold_0_state (v0) (Project.ProofKit.ScalarTransition.U64Op.apply .mul (v1) (v2)) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .mul (v1) (v2)) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) ((0 : UInt64)) (Project.ProofKit.ScalarTransition.U64Op.apply .mul (v1) (v2)) ((1 : UInt64)) (v19) (v20))

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

def function_0_array_fold_0_step_continuingTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  some (function_0_array_fold_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v13) ((1 : UInt64))) (v14) (v15) (v16) (v17) (v18) (v19) (v20))

set_option linter.unusedSimpArgs false in
theorem function_0_array_fold_0_step_continuing_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_0_array_fold_0_step_continuing.evalU64 11
      (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) = function_0_array_fold_0_step_continuingTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
  simp (config := { maxSteps := 1000000 }) only [function_0_array_fold_0_step_continuing, function_0_array_fold_0_state, function_0_array_fold_0_step_continuingTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false]

theorem function_0_array_fold_0_step_continuing_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_0_array_fold_0_step_continuing.eval 11
      (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState =
        (function_0_array_fold_0_step_continuingTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    function_0_array_fold_0_step_continuing_evalU64]

def function_0_array_fold_0_continuing_frame (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) : Wasm.Locals :=
  (function_0_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState.toLocals []

@[simp] theorem function_0_array_fold_0_continuing_frame_params (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).params = [.i64 v0] := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_locals_length (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).locals.length = 20 := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_values (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).values = [] := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 0 = some (.i64 v0) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 1 = some (.i64 v1) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 2 = some (.i64 v2) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 3 = some (.i64 v3) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_4 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 4 = some (.i64 v4) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_5 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 5 = some (.i64 v5) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_6 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 6 = some (.i64 v6) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_7 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 7 = some (.i64 v7) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_8 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 8 = some (.i64 v8) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_9 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 9 = some (.i64 v9) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_10 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 10 = some (.i64 v10) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_11 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 11 = some (.i64 v11) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_12 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 12 = some (.i64 v12) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_13 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 13 = some (.i64 v13) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_14 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 14 = some (.i64 v14) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_15 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 15 = some (.i64 v15) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 16 = some (.i64 v16) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_17 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 17 = some (.i64 v17) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_18 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 18 = some (.i64 v18) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_19 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 19 = some (.i64 v19) := by
  rfl

@[simp] theorem function_0_array_fold_0_continuing_frame_get_20 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).get 20 = some (.i64 v20) := by
  rfl

theorem function_0_array_fold_0_continuing_item_valid (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).validIndex 2 := by
  norm_num [Wasm.Locals.validIndex, function_0_array_fold_0_continuing_frame, function_0_array_fold_0_state,
    Project.ProofKit.ScalarTransition.U64State.toState]

theorem function_0_array_fold_0_continuing_loaded_frame_eq (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) (value : UInt64) :
    Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
      (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) 2 value
      (function_0_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) =
        function_0_array_fold_0_continuing_frame v0 v1 value v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
  simp [Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame,
    function_0_array_fold_0_continuing_frame, function_0_array_fold_0_state,
    Project.ProofKit.ScalarTransition.U64State.toState, Wasm.Locals.set]

theorem function_0_array_fold_0_continuing_spec (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64)
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (input : Array UInt64) (index : Nat)
    (hIndexValue : v13 = UInt64.ofNat index)
    (hContinue : v13 < v15)
    (hInput : Project.ProofKit.UInt64Array.At st v11 input)
    (hIndex : index < input.size)
    (Q : Wasm.Assertion Unit) (rest : Wasm.Program)
    (hNext : Wasm.wp module_ rest Q st
      (Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
        (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) 2 input[index]
        (function_0_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20)) env) :
    Wasm.wp module_ (function_0_array_fold_0_continuing_program ++ rest) Q st
      (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) env := by
  apply Project.ProofKit.FixedArrayTraversalInput.continuingProgram_spec
    (inputPtr := v11) (indexValue := v13)
    (stopValue := v15) (input := input) (index := index)
    (hValues := rfl) (hArrayLocal := rfl) (hIndexLocal := rfl)
    (hStopLocal := rfl) (hIndexValue := hIndexValue)
    (hContinue := hContinue) (hItem := function_0_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20)
    (hInput := hInput) (hIndex := hIndex)
  exact hNext

theorem function_0_array_fold_0_singleton_result_spec (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64)
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (hPayloadBound :
      (Project.ProofKit.FixedArrayResult.payloadAddress v7 0).toUInt32.toNat + 8 ≤
        st.mem.pages * 65536)
    (Q : Wasm.Assertion Unit)
    (hNext : Q (.Fallthrough
      (Project.ProofKit.FixedArrayResult.writePayload st v7 0 v1)
      (Project.ProofKit.FixedArrayResult.finishFrame
        (Project.ProofKit.FixedArrayFold.resultFrame
          (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) 10 v1)
        4 6 v7))) :
    Wasm.wp module_ function_0_array_fold_0_singleton_result_program Q st
      (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) env := by
  change Wasm.wp module_
    (Project.ProofKit.FixedArrayFold.singletonResultProgram
      1 10 7 4
      6) Q st (function_0_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) env
  apply Project.ProofKit.FixedArrayFold.singletonResultProgram_spec_to
    (root := v7) (value := v1)
  · exact function_0_array_fold_0_continuing_frame_values v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
  · exact function_0_array_fold_0_continuing_frame_get_1 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
  · simp only [function_0_array_fold_0_continuing_frame_params]
    norm_num
  · simp [Wasm.Locals.validIndex, function_0_array_fold_0_continuing_frame_params,
      function_0_array_fold_0_continuing_frame_locals_length]
  · apply Project.ProofKit.FixedArrayFold.resultFrame_get_of_ne
    · simp only [function_0_array_fold_0_continuing_frame_params]
      norm_num
    · simp only [function_0_array_fold_0_continuing_frame_params]
      norm_num
    · simp [Wasm.Locals.validIndex, function_0_array_fold_0_continuing_frame_params,
        function_0_array_fold_0_continuing_frame_locals_length]
    · norm_num
    · exact function_0_array_fold_0_continuing_frame_get_7 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
  · apply Project.ProofKit.FixedArrayFold.resultFrame_get_result
    · simp only [function_0_array_fold_0_continuing_frame_params]
      norm_num
    · simp [Wasm.Locals.validIndex, function_0_array_fold_0_continuing_frame_params,
        function_0_array_fold_0_continuing_frame_locals_length]
  · exact hPayloadBound
  · simp only [Project.ProofKit.FixedArrayFold.resultFrame_params,
      function_0_array_fold_0_continuing_frame_params]
    norm_num
  · simp [Wasm.Locals.validIndex,
      Project.ProofKit.FixedArrayFold.resultFrame_params,
      Project.ProofKit.FixedArrayFold.resultFrame_locals_length,
      function_0_array_fold_0_continuing_frame_params, function_0_array_fold_0_continuing_frame_locals_length]
  · simp only [Project.ProofKit.FixedArrayFold.resultFrame_params,
      function_0_array_fold_0_continuing_frame_params]
    norm_num
  · simp [Wasm.Locals.validIndex,
      Project.ProofKit.FixedArrayFold.resultFrame_params,
      Project.ProofKit.FixedArrayFold.resultFrame_locals_length,
      function_0_array_fold_0_continuing_frame_params, function_0_array_fold_0_continuing_frame_locals_length]
  · exact hNext

def function_0_length_dispatch_0_valid_branch_program : Wasm.Program :=
  [
  .constI64 (8 : UInt64),
  .constI64 (1 : UInt64),
  .constI64 (1 : UInt64),
  .mulI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .constI64 (7 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .divUI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .localSet 11,
  .localGet 11,
  .constI64 (8 : UInt64),
  .ltUI64,
  .iff 0 0 [
    .constI64 (8 : UInt64),
    .localSet 11
  ] [],
  .constI64 (0 : UInt64),
  .localSet 16,
  .constI64 (0 : UInt64),
  .localSet 12,
  .globalGet 1,
  .localSet 13,
  .block 0 0 [
    .loop 0 0 [
      .localGet 13,
      .constI64 (0 : UInt64),
      .eqI64,
      .br_if 1,
      .localGet 16,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 13,
      .constI64 (32 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 14,
      .localGet 13,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 15,
      .localGet 14,
      .localGet 11,
      .geUI64,
      .iff 0 0 [
        .localGet 12,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .localGet 15,
          .globalSet 1
        ] [
          .localGet 12,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 15,
          .store64 (0 : UInt32)
        ],
        .localGet 13,
        .constI64 (48 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (5501223100278326855 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (40 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (32 : UInt64),
        .subI64,
        .wrapI64,
        .localGet 14,
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (24 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (2 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (16 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (8 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .localSet 16
      ] [
        .localGet 13,
        .localSet 12,
        .localGet 15,
        .localSet 13
      ],
      .br 0
    ]
  ],
  .localGet 16,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 11,
    .addI64,
    .localSet 14,
    .localGet 14,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 14,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 15,
    .memorySize,
    .extendUI32,
    .localGet 15,
    .ltUI64,
    .iff 0 0 [
      .localGet 15,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const (4294967295 : UInt32),
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localSet 16,
    .localGet 14,
    .globalSet 0,
    .localGet 16,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 11,
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32)
  ] [],
  .globalGet 2,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 2,
  .localGet 16,
  .localSet 7,
  .localGet 7,
  .wrapI64,
  .constI64 (1 : UInt64),
  .store64 (0 : UInt32),
  .localGet 0,
  .localSet 11,
  .localGet 11,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 12,
  .constI64 (0 : UInt64),
  .localSet 13,
  .localGet 0,
  .localSet 16,
  .localGet 16,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 14,
  .constI64 (1 : UInt64),
  .localSet 1,
  .constI64 (0 : UInt64),
  .localSet 18,
  .localGet 14,
  .localGet 12,
  .ltUI64,
  .iff 0 1 [
    .localGet 14
  ] [
    .localGet 12
  ],
  .localSet 15,
  .block 0 0 [
    .loop 0 0 [
      .localGet 13,
      .localGet 15,
      .geUI64,
      .br_if 1,
      .localGet 11,
      .localGet 13,
      .constI64 (1 : UInt64),
      .mulI64,
      .constI64 (1 : UInt64),
      .addI64,
      .constI64 (8 : UInt64),
      .mulI64,
      .addI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 2,
      .localGet 1,
      .localGet 2,
      .mulI64,
      .localSet 3,
      .localGet 3,
      .localSet 17,
      .constI64 (0 : UInt64),
      .localSet 16,
      .localGet 17,
      .localSet 1,
      .constI64 (1 : UInt64),
      .localSet 18,
      .localGet 16,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 13,
      .constI64 (1 : UInt64),
      .addI64,
      .localSet 13,
      .br 0
    ]
  ],
  .localGet 1,
  .localSet 10,
  .localGet 7,
  .constI64 (0 : UInt64),
  .constI64 (1 : UInt64),
  .mulI64,
  .constI64 (1 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 10,
  .store64 (0 : UInt32),
  .localGet 7,
  .localSet 4,
  .localGet 4,
  .localSet 6
]

def function_0_length_dispatch_0_invalid_branch_program : Wasm.Program :=
  [
  .constI64 (8 : UInt64),
  .constI64 (0 : UInt64),
  .constI64 (1 : UInt64),
  .mulI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .constI64 (7 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .divUI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .localSet 11,
  .localGet 11,
  .constI64 (8 : UInt64),
  .ltUI64,
  .iff 0 0 [
    .constI64 (8 : UInt64),
    .localSet 11
  ] [],
  .constI64 (0 : UInt64),
  .localSet 16,
  .constI64 (0 : UInt64),
  .localSet 12,
  .globalGet 1,
  .localSet 13,
  .block 0 0 [
    .loop 0 0 [
      .localGet 13,
      .constI64 (0 : UInt64),
      .eqI64,
      .br_if 1,
      .localGet 16,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 13,
      .constI64 (32 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 14,
      .localGet 13,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 15,
      .localGet 14,
      .localGet 11,
      .geUI64,
      .iff 0 0 [
        .localGet 12,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .localGet 15,
          .globalSet 1
        ] [
          .localGet 12,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 15,
          .store64 (0 : UInt32)
        ],
        .localGet 13,
        .constI64 (48 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (5501223100278326855 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (40 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (32 : UInt64),
        .subI64,
        .wrapI64,
        .localGet 14,
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (24 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (2 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (16 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .constI64 (8 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 13,
        .localSet 16
      ] [
        .localGet 13,
        .localSet 12,
        .localGet 15,
        .localSet 13
      ],
      .br 0
    ]
  ],
  .localGet 16,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 11,
    .addI64,
    .localSet 14,
    .localGet 14,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 14,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 15,
    .memorySize,
    .extendUI32,
    .localGet 15,
    .ltUI64,
    .iff 0 0 [
      .localGet 15,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const (4294967295 : UInt32),
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localSet 16,
    .localGet 14,
    .globalSet 0,
    .localGet 16,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 11,
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 16,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32)
  ] [],
  .globalGet 2,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 2,
  .localGet 16,
  .localSet 7,
  .localGet 7,
  .wrapI64,
  .constI64 (0 : UInt64),
  .store64 (0 : UInt32),
  .localGet 7,
  .localSet 5,
  .localGet 5,
  .localSet 6
]

def function_0_length_dispatch_0_dispatch_program : Wasm.Program :=
  Project.ProofKit.FixedArrayLengthDispatch.leProgram
    7 8
    function_0_length_dispatch_0_valid_branch_program function_0_length_dispatch_0_invalid_branch_program

def function_0_length_dispatch_0_suffix_program : Wasm.Program :=
  [
  .localGet 6
]

theorem function_0_length_dispatch_0_dispatch_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [] 0
      8 = some function_0_length_dispatch_0_dispatch_program := by
  rfl

theorem function_0_length_dispatch_0_function_eq :
    LeanExeGen.GeneratedRa8e90ffc5781d113.func0 =
      function_0_length_dispatch_0_dispatch_program ++ function_0_length_dispatch_0_suffix_program := by
  rfl

def function_0_length_dispatch_0_valid_capacity_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    1 1 11

theorem function_0_length_dispatch_0_valid_capacity_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .thenBranch }] 0
      18 = some function_0_length_dispatch_0_valid_capacity_program := by
  rfl

def function_0_length_dispatch_0_invalid_capacity_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    0 1 11

theorem function_0_length_dispatch_0_invalid_capacity_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRa8e90ffc5781d113.func0
      [{ instructionIndex := 7, field := .elseBranch }] 0
      18 = some function_0_length_dispatch_0_invalid_capacity_program := by
  rfl

end LeanExeGen.GeneratedRa8e90ffc5781d113.AnnotationMatches
