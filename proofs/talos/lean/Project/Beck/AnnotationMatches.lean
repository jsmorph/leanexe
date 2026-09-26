import Project.Beck.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard




import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64











set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.Beck.AnnotationMatches

def function_10_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 4

theorem function_10_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func10
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_10_while_loop_0_guard_program := by
  rfl

theorem function_10_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func10 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_10_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func10 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_10_while_loop_0_condition :
    Project.ProofKit.ScalarTransition.Expr .bool :=
  .and (.not (.eq (.get 0) (.const (0 : UInt64)))) (.eq (.get 4) (.const (0 : UInt64)))

def function_10_while_loop_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .ite (.not (.eq (.ite (.eq (.ite (.eq (.get 2) (.const (0 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.seq (.assign 3 (.get 1)) (.assign 4 (.const (1 : UInt64)))) (.seq (.seq (.seq (.assign 5 (.get 2)) (.assign 6 (.bin .remU (.get 1) (.get 2)))) (.seq (.seq (.seq (.assign 7 (.get 5)) (.assign 8 (.get 6))) (.assign 1 (.get 7))) (.assign 2 (.get 8)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64)))))

def function_10_while_loop_0_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.whileProgram
    9 function_10_while_loop_0_condition function_10_while_loop_0_body

theorem function_10_while_loop_0_eq :
    Project.ProofKit.Annotation.region Project.Beck.func10
      [] 2
      3 = some function_10_while_loop_0_program := by
  rfl

theorem function_10_while_loop_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.Beck.func10 []).getD []).drop 2 =
      Project.Beck.AnnotationMatches.function_10_while_loop_0_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func10 []).getD []).drop 3 := by
  rfl

def function_10_while_loop_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0, v1, v2], locals := [v3, v4, v5, v6, v7, v8, v9, v10] }

def function_10_while_loop_0_conditionTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  (if (!(((v0) == ((0 : UInt64))))) then
      some (((v4) == ((0 : UInt64))), function_10_while_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10)) else
      some (false, function_10_while_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10)))

def function_10_while_loop_0_bodyTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  (if ((v2) == ((0 : UInt64))) then
      some (function_10_while_loop_0_state (v0) (v1) (v2) (v1) ((1 : UInt64)) (v5) (v6) (v7) (v8) (v9) (v10)) else
      some (function_10_while_loop_0_state (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v0) ((1 : UInt64))) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .remU (v1) (v2)) (v3) (v4) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .remU (v1) (v2)) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .remU (v1) (v2)) (v1) (v2)))

set_option linter.unusedSimpArgs false in
theorem function_10_while_loop_0_condition_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    function_10_while_loop_0_condition.evalU64 9
      (function_10_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) = function_10_while_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 := by
  by_cases h0 : ((!(((v0) == ((0 : UInt64)))))) = true
  · simp (config := { maxSteps := 1000000 }) only [function_10_while_loop_0_condition, function_10_while_loop_0_state, function_10_while_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]
  · simp (config := { maxSteps := 1000000 }) only [function_10_while_loop_0_condition, function_10_while_loop_0_state, function_10_while_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]

set_option linter.unusedSimpArgs false in
theorem function_10_while_loop_0_body_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    function_10_while_loop_0_body.evalU64 9
      (function_10_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10) = function_10_while_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 := by
  by_cases h0 : (((v2) == ((0 : UInt64)))) = true
  · simp (config := { maxSteps := 1000000 }) only [function_10_while_loop_0_body, function_10_while_loop_0_state, function_10_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]
  · simp (config := { maxSteps := 1000000 }) only [function_10_while_loop_0_body, function_10_while_loop_0_state, function_10_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]

theorem function_10_while_loop_0_condition_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    function_10_while_loop_0_condition.eval 9
      (function_10_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).toState =
        (function_10_while_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).map fun result =>
          (result.1, result.2.toState) := by
  rw [Project.ProofKit.ScalarTransition.Expr.eval_toState,
    function_10_while_loop_0_condition_evalU64]

theorem function_10_while_loop_0_body_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : UInt64) :
    function_10_while_loop_0_body.eval 9
      (function_10_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).toState =
        (function_10_while_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    function_10_while_loop_0_body_evalU64]

theorem function_10_while_loop_0_loop_tail_eq :
    Project.Beck.func10.drop 2 =
      function_10_while_loop_0_program ++
        Project.Beck.func10.drop 3 := by
  rfl

theorem function_10_while_loop_0_entry_to_loop {α : Type}
    (module : Wasm.Module) (Q : Wasm.Assertion α)
    (initial : Wasm.Store α) (env : Wasm.HostEnv α) (v0 v1 v2 : UInt64) :
    Wasm.wp module Project.Beck.func10 Q initial
      (Project.Beck.func10Def.toLocals [.i64 v0, .i64 v1, .i64 v2]) env ↔
    Wasm.wp module
      (function_10_while_loop_0_program ++
        Project.Beck.func10.drop 3)
      Q initial
      ((function_10_while_loop_0_state (v0) (v1) (v2) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env := by
  rw [← function_10_while_loop_0_loop_tail_eq]
  unfold Project.Beck.func10Def
  unfold Project.Beck.func10
  unfold function_10_while_loop_0_state
  wp_run
  simp [Project.ProofKit.ScalarTransition.U64State.toState,
    Project.ProofKit.ScalarTransition.State.toLocals]

theorem function_10_while_loop_0_terminates_with_of_loop {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α)
    (P : Wasm.Store α → List Wasm.Value → Prop) (v0 v1 v2 : UInt64)
    (hLoop : Wasm.wp Project.Beck.«module»
      (function_10_while_loop_0_program ++
        Project.Beck.func10.drop 3)
      (fun c => match c with
        | .Fallthrough st' s' => P st' (s'.values.take 1)
        | .Return st' vs => P st' (vs.take 1)
        | _ => False)
      initial
      ((function_10_while_loop_0_state (v0) (v1) (v2) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env) :
    Wasm.TerminatesWith env Project.Beck.«module» 10
      initial [.i64 v2, .i64 v1, .i64 v0] P := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := Project.Beck.func10Def) rfl
  unfold Project.Beck.func10Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change Wasm.wp Project.Beck.«module» Project.Beck.func10
    _ initial (Project.Beck.func10Def.toLocals [.i64 v0, .i64 v1, .i64 v2]) env
  rw [function_10_while_loop_0_entry_to_loop]
  exact hLoop

def function_31_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 13

theorem function_31_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.Beck.func31
      [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_31_while_loop_0_guard_program := by
  rfl

theorem function_31_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.Beck.func31 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_31_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.Beck.func31 [{ instructionIndex := 6, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

end Project.Beck.AnnotationMatches
