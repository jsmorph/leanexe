import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64





import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches

def function_0_while_loop_0_condition :
    Project.ProofKit.ScalarTransition.Expr .bool :=
  .and (.not (.eq (.get 0) (.const (0 : UInt64)))) (.eq (.get 5) (.const (0 : UInt64)))

def function_0_while_loop_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .ite (.leU (.get 1) (.const (1 : UInt64))) (.seq (.assign 4 (.get 3)) (.assign 5 (.const (1 : UInt64)))) (.ite (.ltU (.bin .divU (.get 1) (.get 2)) (.get 2)) (.seq (.assign 4 (.bin .add (.get 3) (.const (1 : UInt64)))) (.assign 5 (.const (1 : UInt64)))) (.ite (.not (.eq (.ite (.eq (.ite (.eq (.bin .remU (.get 1) (.get 2)) (.const (0 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.seq (.seq (.seq (.seq (.assign 6 (.bin .divU (.get 1) (.get 2))) (.assign 7 (.get 2))) (.assign 8 (.bin .add (.get 3) (.const (1 : UInt64))))) (.seq (.seq (.seq (.seq (.seq (.assign 9 (.get 6)) (.assign 10 (.get 7))) (.assign 11 (.get 8))) (.assign 1 (.get 9))) (.assign 2 (.get 10))) (.assign 3 (.get 11)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64))))) (.seq (.seq (.seq (.seq (.assign 12 (.get 1)) (.assign 13 (.ite (.not (.eq (.ite (.eq (.ite (.eq (.get 2) (.const (2 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.const (3 : UInt64)) (.bin .add (.get 2) (.const (2 : UInt64)))))) (.assign 14 (.get 3))) (.seq (.seq (.seq (.seq (.seq (.assign 15 (.get 12)) (.assign 16 (.get 13))) (.assign 17 (.get 14))) (.assign 1 (.get 15))) (.assign 2 (.get 16))) (.assign 3 (.get 17)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64)))))))

def function_0_while_loop_0_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.whileProgram
    18 function_0_while_loop_0_condition function_0_while_loop_0_body

theorem function_0_while_loop_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
      [] 2
      3 = some function_0_while_loop_0_program := by
  rfl

def function_0_while_loop_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0, v1, v2, v3], locals := [v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19] }

def function_0_while_loop_0_conditionTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  (if (!(((v0) == ((0 : UInt64))))) then
      some (((v5) == ((0 : UInt64))), function_0_while_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19)) else
      some (false, function_0_while_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19)))

def function_0_while_loop_0_bodyTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  (if (decide ((v1) ≤ ((1 : UInt64)))) then
      some (function_0_while_loop_0_state (v0) (v1) (v2) (v3) (v3) ((1 : UInt64)) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19)) else
      (if (decide ((Project.ProofKit.ScalarTransition.U64Op.apply .divU (v1) (v2)) < (v2))) then
      some (function_0_while_loop_0_state (v0) (v1) (v2) (v3) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v3) ((1 : UInt64))) ((1 : UInt64)) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v1) (v2)) else
      (if ((Project.ProofKit.ScalarTransition.U64Op.apply .remU (v1) (v2)) == ((0 : UInt64))) then
      some (function_0_while_loop_0_state (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v0) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (v1) (v2)) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v3) ((1 : UInt64))) (v4) (v5) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (v1) (v2)) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v3) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .divU (v1) (v2)) (v2) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v3) ((1 : UInt64))) (v12) (v13) (v14) (v15) (v16) (v17) (v1) (v2)) else
      (if ((v2) == ((2 : UInt64))) then
      some (function_0_while_loop_0_state (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v0) ((1 : UInt64))) (v1) ((3 : UInt64)) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v1) ((3 : UInt64)) (v3) (v1) ((3 : UInt64)) (v3) (v1) (v2)) else
      some (function_0_while_loop_0_state (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v0) ((1 : UInt64))) (v1) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) ((2 : UInt64))) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v1) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) ((2 : UInt64))) (v3) (v1) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v2) ((2 : UInt64))) (v3) (v1) (v2))))))

set_option linter.unusedSimpArgs false in
theorem function_0_while_loop_0_condition_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    function_0_while_loop_0_condition.evalU64 18
      (function_0_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19) = function_0_while_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 := by
  by_cases h0 : ((!(((v0) == ((0 : UInt64)))))) = true
  · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_condition, function_0_while_loop_0_state, function_0_while_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]
  · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_condition, function_0_while_loop_0_state, function_0_while_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]

set_option linter.unusedSimpArgs false in
theorem function_0_while_loop_0_body_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    function_0_while_loop_0_body.evalU64 18
      (function_0_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19) = function_0_while_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 := by
  by_cases h0 : ((decide ((v1) ≤ ((1 : UInt64))))) = true
  · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_body, function_0_while_loop_0_state, function_0_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0]
  · by_cases h1 : ((decide ((Project.ProofKit.ScalarTransition.U64Op.apply .divU (v1) (v2)) < (v2)))) = true
    · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_body, function_0_while_loop_0_state, function_0_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]
    · by_cases h2 : (((Project.ProofKit.ScalarTransition.U64Op.apply .remU (v1) (v2)) == ((0 : UInt64)))) = true
      · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_body, function_0_while_loop_0_state, function_0_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1, h2]
      · by_cases h3 : (((v2) == ((2 : UInt64)))) = true
        · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_body, function_0_while_loop_0_state, function_0_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1, h2, h3]
        · simp (config := { maxSteps := 1000000 }) only [function_0_while_loop_0_body, function_0_while_loop_0_state, function_0_while_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1, h2, h3]

theorem function_0_while_loop_0_condition_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    function_0_while_loop_0_condition.eval 18
      (function_0_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState =
        (function_0_while_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).map fun result =>
          (result.1, result.2.toState) := by
  rw [Project.ProofKit.ScalarTransition.Expr.eval_toState,
    function_0_while_loop_0_condition_evalU64]

theorem function_0_while_loop_0_body_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    function_0_while_loop_0_body.eval 18
      (function_0_while_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState =
        (function_0_while_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    function_0_while_loop_0_body_evalU64]

theorem function_0_while_loop_0_loop_tail_eq :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func0.drop 2 =
      function_0_while_loop_0_program ++
        LeanExeGen.GeneratedRbade8cb1a4e3a423.func0.drop 3 := by
  rfl

theorem function_0_while_loop_0_entry_to_loop {α : Type}
    (module : Wasm.Module) (Q : Wasm.Assertion α)
    (initial : Wasm.Store α) (env : Wasm.HostEnv α) (v0 v1 v2 v3 : UInt64) :
    Wasm.wp module LeanExeGen.GeneratedRbade8cb1a4e3a423.func0 Q initial
      (LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def.toLocals [.i64 v0, .i64 v1, .i64 v2, .i64 v3]) env ↔
    Wasm.wp module
      (function_0_while_loop_0_program ++
        LeanExeGen.GeneratedRbade8cb1a4e3a423.func0.drop 3)
      Q initial
      ((function_0_while_loop_0_state (v0) (v1) (v2) (v3) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env := by
  rw [← function_0_while_loop_0_loop_tail_eq]
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
  unfold function_0_while_loop_0_state
  wp_run
  simp [Project.ProofKit.ScalarTransition.U64State.toState,
    Project.ProofKit.ScalarTransition.State.toLocals]

theorem function_0_while_loop_0_terminates_with_of_loop {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α)
    (P : Wasm.Store α → List Wasm.Value → Prop) (v0 v1 v2 v3 : UInt64)
    (hLoop : Wasm.wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module»
      (function_0_while_loop_0_program ++
        LeanExeGen.GeneratedRbade8cb1a4e3a423.func0.drop 3)
      (fun c => match c with
        | .Fallthrough st' s' => P st' (s'.values.take 1)
        | .Return st' vs => P st' (vs.take 1)
        | _ => False)
      initial
      ((function_0_while_loop_0_state (v0) (v1) (v2) (v3) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» 0
      initial [.i64 v3, .i64 v2, .i64 v1, .i64 v0] P := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def) rfl
  unfold LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change Wasm.wp LeanExeGen.GeneratedRbade8cb1a4e3a423.«module» LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
    _ initial (LeanExeGen.GeneratedRbade8cb1a4e3a423.func0Def.toLocals [.i64 v0, .i64 v1, .i64 v2, .i64 v3]) env
  rw [function_0_while_loop_0_entry_to_loop]
  exact hLoop

def function_2_singleton_wrapper_0 : Wasm.Program :=
  Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram
    1

theorem function_2_singleton_wrapper_0_eq :
    LeanExeGen.GeneratedRbade8cb1a4e3a423.func2 = function_2_singleton_wrapper_0 := by
  rfl

end LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
