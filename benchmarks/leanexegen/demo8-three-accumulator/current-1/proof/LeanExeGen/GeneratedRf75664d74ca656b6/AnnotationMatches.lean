import LeanExeGen.GeneratedRf75664d74ca656b6.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64





import Project.ProofKit.FixedArraySingletonWrapper

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace LeanExeGen.GeneratedRf75664d74ca656b6.AnnotationMatches

def function_0_scalar_post_test_loop_0_condition :
    Project.ProofKit.ScalarTransition.Expr .bool :=
  .ne (.get 19) (.const (0 : UInt64))

def function_0_scalar_post_test_loop_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.assign 7 (.get 4)) (.assign 8 (.get 5))) (.assign 9 (.get 6))) (.assign 10 (.get 8))) (.assign 11 (.get 9))) (.ite (.not (.eq (.ite (.eq (.ite (.not (.not (.eq (.ite (.eq (.get 10) (.const (0 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64))))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.seq (.seq (.seq (.seq (.seq (.assign 12 (.bin .sub (.get 10) (.const (1 : UInt64)))) (.assign 13 (.bin .add (.get 11) (.const (1 : UInt64))))) (.assign 14 (.bin .add (.get 7) (.const (2 : UInt64))))) (.assign 15 (.get 14))) (.assign 16 (.get 12))) (.assign 17 (.get 13))) (.seq (.seq (.assign 15 (.get 7)) (.assign 16 (.get 10))) (.assign 17 (.get 11))))) (.seq (.seq (.assign 20 (.get 15)) (.assign 21 (.get 16))) (.assign 22 (.get 17)))) (.assign 19 (.ite (.not (.eq (.ite (.eq (.ite (.not (.not (.eq (.ite (.eq (.get 5) (.const (0 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64))))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.const (0 : UInt64)) (.const (1 : UInt64))))) (.seq (.seq (.assign 4 (.get 20)) (.assign 5 (.get 21))) (.assign 6 (.get 22)))) (.assign 23 (.const (1 : UInt64)))

def function_0_scalar_post_test_loop_0_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.postTestProgram
    19 function_0_scalar_post_test_loop_0_condition function_0_scalar_post_test_loop_0_body

theorem function_0_scalar_post_test_loop_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRf75664d74ca656b6.func0
      [] 14
      15 = some function_0_scalar_post_test_loop_0_program := by
  rfl

def function_0_scalar_post_test_loop_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0], locals := [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23] }

def function_0_scalar_post_test_loop_0_conditionTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    Option (Bool × Project.ProofKit.ScalarTransition.U64State) :=
  some (((v19) != ((0 : UInt64))), function_0_scalar_post_test_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20) (v21) (v22) (v23))

def function_0_scalar_post_test_loop_0_bodyTransition (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    Option Project.ProofKit.ScalarTransition.U64State :=
  (if ((v5) == ((0 : UInt64))) then
      (if ((v5) == ((0 : UInt64))) then
      some (function_0_scalar_post_test_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v4) (v5) (v6) (v5) (v6) (v12) (v13) (v14) (v4) (v5) (v6) (v18) ((1 : UInt64)) (v4) (v5) (v6) ((1 : UInt64))) else
      some (function_0_scalar_post_test_loop_0_state (v0) (v1) (v2) (v3) (v4) (v5) (v6) (v4) (v5) (v6) (v5) (v6) (v12) (v13) (v14) (v4) (v5) (v6) (v18) ((0 : UInt64)) (v4) (v5) (v6) ((1 : UInt64)))) else
      (if ((v5) == ((0 : UInt64))) then
      some (function_0_scalar_post_test_loop_0_state (v0) (v1) (v2) (v3) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) (v4) (v5) (v6) (v5) (v6) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) (v18) ((1 : UInt64)) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) ((1 : UInt64))) else
      some (function_0_scalar_post_test_loop_0_state (v0) (v1) (v2) (v3) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) (v4) (v5) (v6) (v5) (v6) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) (v18) ((0 : UInt64)) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .sub (v5) ((1 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v6) ((1 : UInt64))) ((1 : UInt64)))))

set_option linter.unusedSimpArgs false in
theorem function_0_scalar_post_test_loop_0_condition_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    function_0_scalar_post_test_loop_0_condition.evalU64 19
      (function_0_scalar_post_test_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23) = function_0_scalar_post_test_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 := by
  simp (config := { maxSteps := 1000000 }) only [function_0_scalar_post_test_loop_0_condition, function_0_scalar_post_test_loop_0_state, function_0_scalar_post_test_loop_0_conditionTransition, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false]

set_option linter.unusedSimpArgs false in
theorem function_0_scalar_post_test_loop_0_body_evalU64 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    function_0_scalar_post_test_loop_0_body.evalU64 19
      (function_0_scalar_post_test_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23) = function_0_scalar_post_test_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 := by
  by_cases h0 : (((v5) == ((0 : UInt64)))) = true
  · by_cases h1 : (((v5) == ((0 : UInt64)))) = true
    · simp (config := { maxSteps := 1000000 }) only [function_0_scalar_post_test_loop_0_body, function_0_scalar_post_test_loop_0_state, function_0_scalar_post_test_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]
    · simp (config := { maxSteps := 1000000 }) only [function_0_scalar_post_test_loop_0_body, function_0_scalar_post_test_loop_0_state, function_0_scalar_post_test_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]
  · by_cases h1 : (((v5) == ((0 : UInt64)))) = true
    · simp (config := { maxSteps := 1000000 }) only [function_0_scalar_post_test_loop_0_body, function_0_scalar_post_test_loop_0_state, function_0_scalar_post_test_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]
    · simp (config := { maxSteps := 1000000 }) only [function_0_scalar_post_test_loop_0_body, function_0_scalar_post_test_loop_0_state, function_0_scalar_post_test_loop_0_bodyTransition, Project.ProofKit.ScalarTransition.Stmt.evalU64, Project.ProofKit.ScalarTransition.Expr.evalU64, Project.ProofKit.ScalarTransition.U64State.get, Project.ProofKit.ScalarTransition.U64State.set?, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.map, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceCtorEq, or_true, true_or, or_false, false_or, Bool.false_eq_true, Bool.not_eq_true', Bool.not_true, Bool.not_false, beq_self_eq_true, Project.ProofKit.ScalarTransition.u64_one_beq_zero, Project.ProofKit.ScalarTransition.u64_zero_beq_one, decide_true, decide_false, if_true, if_false, h0, h1]

theorem function_0_scalar_post_test_loop_0_condition_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    function_0_scalar_post_test_loop_0_condition.eval 19
      (function_0_scalar_post_test_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23).toState =
        (function_0_scalar_post_test_loop_0_conditionTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23).map fun result =>
          (result.1, result.2.toState) := by
  rw [Project.ProofKit.ScalarTransition.Expr.eval_toState,
    function_0_scalar_post_test_loop_0_condition_evalU64]

theorem function_0_scalar_post_test_loop_0_body_eval (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64) :
    function_0_scalar_post_test_loop_0_body.eval 19
      (function_0_scalar_post_test_loop_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23).toState =
        (function_0_scalar_post_test_loop_0_bodyTransition v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23).map
          Project.ProofKit.ScalarTransition.U64State.toState := by
  rw [Project.ProofKit.ScalarTransition.Stmt.eval_toState,
    function_0_scalar_post_test_loop_0_body_evalU64]

theorem function_0_scalar_post_test_loop_0_loop_tail_eq :
    LeanExeGen.GeneratedRf75664d74ca656b6.func0.drop 14 =
      function_0_scalar_post_test_loop_0_program ++
        LeanExeGen.GeneratedRf75664d74ca656b6.func0.drop 15 := by
  rfl

theorem function_0_scalar_post_test_loop_0_entry_to_loop {α : Type}
    (module : Wasm.Module) (Q : Wasm.Assertion α)
    (initial : Wasm.Store α) (env : Wasm.HostEnv α) (v0 : UInt64) :
    Wasm.wp module LeanExeGen.GeneratedRf75664d74ca656b6.func0 Q initial
      (LeanExeGen.GeneratedRf75664d74ca656b6.func0Def.toLocals [.i64 v0]) env ↔
    Wasm.wp module
      (function_0_scalar_post_test_loop_0_program ++
        LeanExeGen.GeneratedRf75664d74ca656b6.func0.drop 15)
      Q initial
      ((function_0_scalar_post_test_loop_0_state (v0) (v0) (v0) ((0 : UInt64)) (v0) (v0) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env := by
  rw [← function_0_scalar_post_test_loop_0_loop_tail_eq]
  unfold LeanExeGen.GeneratedRf75664d74ca656b6.func0Def
  unfold LeanExeGen.GeneratedRf75664d74ca656b6.func0
  unfold function_0_scalar_post_test_loop_0_state
  wp_run
  simp [Project.ProofKit.ScalarTransition.U64State.toState,
    Project.ProofKit.ScalarTransition.State.toLocals]

theorem function_0_scalar_post_test_loop_0_terminates_with_of_loop {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α)
    (P : Wasm.Store α → List Wasm.Value → Prop) (v0 : UInt64)
    (hLoop : Wasm.wp LeanExeGen.GeneratedRf75664d74ca656b6.«module»
      (function_0_scalar_post_test_loop_0_program ++
        LeanExeGen.GeneratedRf75664d74ca656b6.func0.drop 15)
      (fun c => match c with
        | .Fallthrough st' s' => P st' (s'.values.take 1)
        | .Return st' vs => P st' (vs.take 1)
        | _ => False)
      initial
      ((function_0_scalar_post_test_loop_0_state (v0) (v0) (v0) ((0 : UInt64)) (v0) (v0) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64)) ((0 : UInt64))).toState.toLocals []) env) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRf75664d74ca656b6.«module» 0
      initial [.i64 v0] P := by
  apply Wasm.TerminatesWith.of_wp_entry_for
    (f := LeanExeGen.GeneratedRf75664d74ca656b6.func0Def) rfl
  unfold LeanExeGen.GeneratedRf75664d74ca656b6.func0Def
  simp only [Wasm.Function.numParams, List.length, List.take, List.reverse_cons,
    List.reverse_nil, List.drop, Nat.zero_add, List.append_nil]
  change Wasm.wp LeanExeGen.GeneratedRf75664d74ca656b6.«module» LeanExeGen.GeneratedRf75664d74ca656b6.func0
    _ initial (LeanExeGen.GeneratedRf75664d74ca656b6.func0Def.toLocals [.i64 v0]) env
  rw [function_0_scalar_post_test_loop_0_entry_to_loop]
  exact hLoop

theorem function_0_scalar_post_test_loop_0_terminates_with_counter_transfer_identity {α : Type}
    (env : Wasm.HostEnv α) (initial : Wasm.Store α) (input : UInt64) :
    Wasm.TerminatesWith env LeanExeGen.GeneratedRf75664d74ca656b6.«module» 0
      initial [.i64 input]
      (fun final results => final = initial ∧ results = [.i64 input]) := by
  apply function_0_scalar_post_test_loop_0_terminates_with_of_loop
  let View : Project.ProofKit.ScalarTransition.State → UInt64 → UInt64 → Prop :=
    fun current remaining result =>
      ∃ v1 v2 v3 v4 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : UInt64,
        current = (function_0_scalar_post_test_loop_0_state (input) (v1) (v2) (v3) (v4) (remaining) (result) (v7) (v8) (v9) (v10) (v11) (v12) (v13) (v14) (v15) (v16) (v17) (v18) (v19) (v20) (v21) (v22) (v23)).toState
  let remainingOf : Project.ProofKit.ScalarTransition.State → UInt64 := fun current =>
    match current.locals[4]? with
    | some (Wasm.Value.i64 remaining) => remaining
    | _ => 0
  unfold function_0_scalar_post_test_loop_0_program
  apply Project.ProofKit.ScalarTransition.CounterTransition.postTestProgram_spec
    (remainingOf := remainingOf) (View := View)
    (initialRemaining := input) (initialResult := 0) (expected := input)
  · intro current remaining result hView
    rcases hView with ⟨v1, v2, v3, v4, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, rfl⟩
    simp [remainingOf, function_0_scalar_post_test_loop_0_state,
      Project.ProofKit.ScalarTransition.U64State.toState]
  · dsimp [View]
    exact ⟨input, input, (0 : UInt64), input, (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), rfl⟩
  · simp
  · intro current remaining result hView hZero hResult
    rcases hView with ⟨v1, v2, v3, v4, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, rfl⟩
    subst remaining
    subst result
    let after := (function_0_scalar_post_test_loop_0_state (input) (v1) (v2) (v3) (v4) ((0 : UInt64)) (input) (v4) ((0 : UInt64)) (input) ((0 : UInt64)) (input) (v12) (v13) (v14) (v4) ((0 : UInt64)) (input) (v18) ((1 : UInt64)) (v4) ((0 : UInt64)) (input) ((1 : UInt64))).toState
    refine ⟨after, after, ?_, ?_, ?_⟩
    · rw [function_0_scalar_post_test_loop_0_body_eval]
      simp [function_0_scalar_post_test_loop_0_bodyTransition,
        Project.ProofKit.ScalarTransition.U64Op.apply, after]
    · rw [function_0_scalar_post_test_loop_0_condition_eval]
      simp [function_0_scalar_post_test_loop_0_conditionTransition, after]
    · unfold LeanExeGen.GeneratedRf75664d74ca656b6.func0
      wp_run
      simp [after, function_0_scalar_post_test_loop_0_state,
        Project.ProofKit.ScalarTransition.U64State.toState,
        Project.ProofKit.ScalarTransition.State.toLocals]
  · intro current remaining result hView hZero
    rcases hView with ⟨v1, v2, v3, v4, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, rfl⟩
    let remaining' := Project.ProofKit.ScalarTransition.U64Op.apply .sub remaining 1
    let result' := Project.ProofKit.ScalarTransition.U64Op.apply .add result 1
    let after := (function_0_scalar_post_test_loop_0_state (input) (v1) (v2) (v3) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (remaining') (result') (v4) (remaining) (result) (remaining) (result) (remaining') (result') (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (remaining') (result') (v18) ((0 : UInt64)) (Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64))) (remaining') (result') ((1 : UInt64))).toState
    refine ⟨after, after, ?_, ?_, ?_⟩
    · rw [function_0_scalar_post_test_loop_0_body_eval]
      simp [function_0_scalar_post_test_loop_0_bodyTransition,
        Project.ProofKit.ScalarTransition.U64Op.apply,
        hZero, remaining', result', after]
    · rw [function_0_scalar_post_test_loop_0_condition_eval]
      simp [function_0_scalar_post_test_loop_0_conditionTransition, after]
    · dsimp [View]
      exact ⟨v1, v2, v3, Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64)), v4, remaining, result, remaining, result, remaining', result', Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64)), Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64)), remaining', result', v18, (0 : UInt64), Project.ProofKit.ScalarTransition.U64Op.apply .add (v4) ((2 : UInt64)), remaining', result', (1 : UInt64), rfl⟩

def function_1_singleton_wrapper_0 : Wasm.Program :=
  Project.ProofKit.FixedArraySingletonWrapper.wrapperProgram
    0

theorem function_1_singleton_wrapper_0_eq :
    LeanExeGen.GeneratedRf75664d74ca656b6.func1 = function_1_singleton_wrapper_0 := by
  rfl

end LeanExeGen.GeneratedRf75664d74ca656b6.AnnotationMatches
