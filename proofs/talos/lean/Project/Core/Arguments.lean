import Project.Compiler.ScalarEvaluation

namespace Project.Core

open LeanExe.Wasm.ScalarDescriptor (Expr)
open Project.ProofKit.ScalarTransition (State)
open Project.Compiler.ScalarLowering (Agrees capacity)

def argumentsCode (expressions : List Expr) (scratch : Nat) : Wasm.Program :=
  expressions.flatMap fun expression =>
    (Project.Compiler.ScalarLowering.expression expression).program scratch

def argumentsWidth : List Expr → Nat
  | [] => 0
  | expression :: rest => max expression.scratchWidth (argumentsWidth rest)

def argumentsEval (expressions : List Expr) (source : List UInt64) : Option (List UInt64) :=
  expressions.mapM fun expression => expression.eval source

@[simp] theorem argumentsCode_nil (scratch : Nat) :
    argumentsCode [] scratch = [] := rfl

@[simp] theorem argumentsCode_cons (expression : Expr) (expressions : List Expr)
    (scratch : Nat) :
    argumentsCode (expression :: expressions) scratch =
      (Project.Compiler.ScalarLowering.expression expression).program scratch ++
        argumentsCode expressions scratch := rfl

@[simp] theorem argumentsEval_nil (source : List UInt64) :
    argumentsEval [] source = some [] := rfl

@[simp] theorem argumentsEval_cons (expression : Expr) (expressions : List Expr)
    (source : List UInt64) :
    argumentsEval (expression :: expressions) source = (do
      let value ← expression.eval source
      let values ← argumentsEval expressions source
      pure (value :: values)) := by
  simp only [argumentsEval, List.mapM_cons]

theorem argumentsEval_length {expressions : List Expr} {source args : List UInt64}
    (evaluated : argumentsEval expressions source = some args) :
    args.length = expressions.length := by
  induction expressions generalizing args with
  | nil =>
      simp only [argumentsEval_nil, Option.some.injEq] at evaluated
      subst args
      rfl
  | cons expression expressions ih =>
      simp only [argumentsEval_cons, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at evaluated
      obtain ⟨value, _, values, evaluated, rfl⟩ := evaluated
      simpa only [List.length_cons] using congrArg Nat.succ (ih evaluated)

/-- Evaluate arguments in source order and place their values in Wasm operand-stack
order. Only scratch locals can change; the store and live source locals are preserved. -/
theorem arguments_execution (expressions : List Expr) (scratch : Nat)
    {source : List UInt64} {state : State} {args : List UInt64}
    (evaluated : argumentsEval expressions source = some args)
    (agree : Agrees source state) (above : source.length ≤ scratch)
    (room : scratch + argumentsWidth expressions ≤ capacity state)
    (values : List Wasm.Value) (module_ : Wasm.Module) (env : Wasm.HostEnv α)
    (store : Wasm.Store α) :
    ∃ next, Agrees source next ∧ capacity next = capacity state ∧
      ∀ (rest : Wasm.Program) (Q : Wasm.Assertion α),
        Wasm.wp module_ rest Q store
          (next.toLocals ((args.map Wasm.Value.i64).reverse ++ values)) env →
        Wasm.wp module_ (argumentsCode expressions scratch ++ rest) Q store
          (state.toLocals values) env := by
  induction expressions generalizing state args values with
  | nil =>
      simp only [argumentsEval_nil, Option.some.injEq] at evaluated
      subst args
      refine ⟨state, agree, rfl, ?_⟩
      intro rest Q continuation
      simpa using continuation
  | cons expression expressions ih =>
      simp only [argumentsEval_cons, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at evaluated
      obtain ⟨value, expressionEval, args, argumentsEval, rfl⟩ := evaluated
      simp only [argumentsWidth] at room
      obtain ⟨afterExpression, expressionComputed, expressionAgree, expressionSize⟩ :=
        Project.Compiler.ScalarLowering.expression_eval expression scratch
          expressionEval agree above (by omega)
      obtain ⟨next, nextAgree, nextSize, argumentsSpec⟩ :=
        ih (state := afterExpression) (args := args)
          argumentsEval expressionAgree (by omega) (.i64 value :: values)
      refine ⟨next, nextAgree, nextSize.trans expressionSize, ?_⟩
      intro rest Q continuation
      rw [argumentsCode_cons, List.append_assoc]
      apply Project.ProofKit.ScalarTransition.Expr.program_spec
        (Project.Compiler.ScalarLowering.expression expression) scratch state
        afterExpression value values module_ env store
        (argumentsCode expressions scratch ++ rest) Q expressionComputed
      apply argumentsSpec rest Q
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using continuation

end Project.Core
