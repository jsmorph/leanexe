import Project.Drone.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard




import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64











set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.Drone.AnnotationMatches

def function_0_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 5

theorem function_0_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func0
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_0_while_loop_0_guard_program := by
  rfl

theorem function_0_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func0 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_0_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func0 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_6_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 5

theorem function_6_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func6
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_6_while_loop_0_guard_program := by
  rfl

theorem function_6_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func6 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_6_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func6 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_6_while_loop_0_condition :
    Project.ProofKit.ScalarTransition.Expr .bool :=
  .and (.not (.eq (.get 0) (.const (0 : UInt64)))) (.eq (.get 5) (.const (0 : UInt64)))

def function_6_while_loop_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .ite (.ltU (.get 2) (.get 3)) (.seq (.assign 6 (.bin .divU (.bin .add (.get 2) (.get 3)) (.const (2 : UInt64)))) (.ite (.ltU (.bin .mul (.get 6) (.get 6)) (.get 1)) (.seq (.seq (.seq (.seq (.assign 7 (.get 1)) (.assign 8 (.bin .add (.get 6) (.const (1 : UInt64))))) (.assign 9 (.get 3))) (.seq (.seq (.seq (.seq (.seq (.assign 10 (.get 7)) (.assign 11 (.get 8))) (.assign 12 (.get 9))) (.assign 1 (.get 10))) (.assign 2 (.get 11))) (.assign 3 (.get 12)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64))))) (.seq (.seq (.seq (.seq (.assign 13 (.get 1)) (.assign 14 (.get 2))) (.assign 15 (.get 6))) (.seq (.seq (.seq (.seq (.seq (.assign 16 (.get 13)) (.assign 17 (.get 14))) (.assign 18 (.get 15))) (.assign 1 (.get 16))) (.assign 2 (.get 17))) (.assign 3 (.get 18)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64))))))) (.seq (.assign 4 (.get 2)) (.assign 5 (.const (1 : UInt64))))

def function_6_while_loop_0_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.whileProgram
    19 function_6_while_loop_0_condition function_6_while_loop_0_body

theorem function_6_while_loop_0_eq :
    Project.ProofKit.Annotation.region Project.Drone.func6
      [] 2
      3 = some function_6_while_loop_0_program := by
  rfl

theorem function_6_while_loop_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.Drone.func6 []).getD []).drop 2 =
      Project.Drone.AnnotationMatches.function_6_while_loop_0_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func6 []).getD []).drop 3 := by
  rfl

def function_6_while_loop_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0, v1, v2, v3], locals := [v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20] }

def function_6_while_loop_0_conditionTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  (if (!(((v0) == ((0 : UInt64))))) then
      some (((v5) == ((0 : UInt64))), function_6_while_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20)) else
      some (false, function_6_while_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20)))

def function_6_while_loop_0_bodyTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  (if (decide ((v2) < (v3))) then
      (if (decide ((Project.ProofKit.ScalarTransition.U64Op.apply .mul (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64)))) < (v1))) then
      some (function_6_while_loop_0_state (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v0) ((1 : UInt64))) (v1) (Project.ProofKit.ScalarTransition.U64Op.apply .add (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) ((1 : UInt64))) (v3) (v4) (v5) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (v1) (Project.ProofKit.ScalarTransition.U64Op.apply .add (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) ((1 : UInt64))) (v3) (v1) (Project.ProofKit.ScalarTransition.U64Op.apply .add (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) ((1 : UInt64))) (v3) (v13) (v14) (v15) (v16) (v17) (v18) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) else
      some (function_6_while_loop_0_state (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v0) ((1 : UInt64))) (v1) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (v4) (v5) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (v7) (v8) (v9) (v10) (v11) (v12) (v1) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (v1) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64)))) else
      some (function_6_while_loop_0_state (v0) (v1) (v2) (v3) (v2) ((1 : UInt64)) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20)))

set_option linter.unusedSimpArgs false in
theorem function_6_while_loop_0_condition_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_6_while_loop_0_condition.evalU64 19
      (function_6_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) = function_6_while_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
  by_cases h0 : ((!(((v0) == ((0 : UInt64)))))) = true
  · simp (config := { maxSteps := 1000000 }) only [function_6_while_loop_0_condition, function_6_while_loop_0_state, function_6_while_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]
  · simp (config := { maxSteps := 1000000 }) only [function_6_while_loop_0_condition, function_6_while_loop_0_state, function_6_while_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]

set_option linter.unusedSimpArgs false in
theorem function_6_while_loop_0_body_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_6_while_loop_0_body.evalU64 19
      (function_6_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20) = function_6_while_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 := by
  by_cases h0 : ((decide ((v2) < (v3)))) = true
  · by_cases h1 : ((decide ((Project.ProofKit.ScalarTransition.U64Op.apply .mul (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) (v3)) ((2 : UInt64)))) < (v1)))) = true
    · simp (config := { maxSteps := 1000000 }) only [function_6_while_loop_0_body, function_6_while_loop_0_state, function_6_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]
    · simp (config := { maxSteps := 1000000 }) only [function_6_while_loop_0_body, function_6_while_loop_0_state, function_6_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]
  · simp (config := { maxSteps := 1000000 }) only [function_6_while_loop_0_body, function_6_while_loop_0_state, function_6_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]

theorem function_6_while_loop_0_condition_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_6_while_loop_0_condition.eval 19
      (function_6_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState =
        (function_6_while_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).map fun result =>
          (result.1, result.2.toState) := by
  rw [Project.ProofKit.ScalarTransition.Expr.eval_toState,
    function_6_while_loop_0_condition_evalU64]

theorem function_6_while_loop_0_body_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 : UInt64) :
    function_6_while_loop_0_body.eval 19
      (function_6_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).toState =
        (function_6_while_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    function_6_while_loop_0_body_evalU64]

theorem function_6_while_loop_0_loop_tail_eq :
    Project.Drone.func6.drop 2 =
      function_6_while_loop_0_program ++
        Project.Drone.func6.drop 3 := by
  rfl

theorem function_6_while_loop_0_entry_to_loop {α : Type}
    (module : Wasm.Module) (Q : Wasm.Assertion α)
    (initial : Wasm.Store α) (env : Wasm.HostEnv α) (v0 v1 v2 v3 : UInt64) :
    Wasm.wp module Project.Drone.func6 Q initial
      (Project.Drone.func6Def.toLocals [.i64 v0, .i64 v1, .i64 v2, .i64 v3]) env ↔
    Wasm.wp module
      (function_6_while_loop_0_program ++
        Project.Drone.func6.drop 3)
      Q initial
      ((function_6_while_loop_0_state (v0) (v1) (v2) (v3) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env := by
  rw [← function_6_while_loop_0_loop_tail_eq]
  unfold Project.Drone.func6Def
  unfold Project.Drone.func6
  unfold function_6_while_loop_0_state
  wp_run
  simp [Project.ProofKit.ScalarTransition.U64State.toState,
    Project.ProofKit.ScalarTransition.State.toLocals]

theorem function_6_while_loop_0_terminates_with_of_loop {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α)
    (P : Wasm.Store α → List Wasm.Value → Prop) (v0 v1 v2 v3 : UInt64)
    (hLoop : Wasm.wp Project.Drone.«module»
      (function_6_while_loop_0_program ++
        Project.Drone.func6.drop 3)
      (fun c => match c with
        | .Fallthrough st' s' => P st' (s'.values.take 1)
        | .Return st' vs => P st' (vs.take 1)
        | _ => False)
      initial
      ((function_6_while_loop_0_state (v0) (v1) (v2) (v3) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env) :
    Wasm.TerminatesWith env Project.Drone.«module» 6
      initial [.i64 v3, .i64 v2, .i64 v1, .i64 v0] P := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := Project.Drone.func6Def) rfl
  unfold Project.Drone.func6Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change Wasm.wp Project.Drone.«module» Project.Drone.func6
    _ initial (Project.Drone.func6Def.toLocals [.i64 v0, .i64 v1, .i64 v2, .i64 v3]) env
  rw [function_6_while_loop_0_entry_to_loop]
  exact hLoop

def function_14_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 14

theorem function_14_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func14
      [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_14_while_loop_0_guard_program := by
  rfl

theorem function_14_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func14 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_14_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func14 [{ instructionIndex := 4, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_18_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 13

theorem function_18_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func18
      [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_18_while_loop_0_guard_program := by
  rfl

theorem function_18_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func18 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_18_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func18 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_21_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 10

theorem function_21_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func21
      [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_21_while_loop_0_guard_program := by
  rfl

theorem function_21_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func21 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_21_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func21 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_22_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 13

theorem function_22_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func22
      [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_22_while_loop_0_guard_program := by
  rfl

theorem function_22_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func22 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_22_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func22 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_24_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 14

theorem function_24_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Drone.func24
      [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_24_while_loop_0_guard_program := by
  rfl

theorem function_24_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Drone.func24 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_24_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Drone.func24 [{ instructionIndex := 8, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.Drone.AnnotationMatches
