import LeanExe.Wasm.ScalarSemantics

namespace LeanExe.Core

open LeanExe.Wasm.ScalarDescriptor (Expr Cond)

/-- First-order control and effects. Compound data operations are library calls;
the compiler has one call rule, including recursive and mutually recursive calls. -/
inductive Stmt where
  | skip
  | assign (destination : Nat) (value : Expr)
  | seq (first second : Stmt)
  | branch (condition : Cond) (yes no : Stmt)
  | loop (condition : Cond) (body : Stmt)
  | call (destination function : Nat) (arguments : List Expr)
  | effect (destination operation : Nat) (arguments : List Expr)

structure Function where
  params : Nat
  locals : Nat
  body : Stmt
  result : Expr

abbrev Module := List Function
abbrev Locals := List UInt64

def arguments (expressions : List Expr) (locals : Locals) : Option (List UInt64) :=
  expressions.mapM (·.eval locals)

/-- Effects have Lean meanings on an explicit native state, including the input
and output used by I/O. Primitive correctness is proved for that same state. -/
abbrev Effects (σ : Type) := Nat → List UInt64 → σ → UInt64 → σ → Prop

/-- Native evaluation of the core. The arithmetic and condition evaluators use
Lean's UInt64 and Bool definitions. Loops may contain arbitrary statements;
calls may target any function, including their caller. -/
inductive Eval (functions : Module) (effects : Effects σ) :
    Stmt → σ → Locals → σ → Locals → Prop where
  | skip : Eval functions effects .skip world locals world locals
  | assign (evaluated : expression.eval locals = some value)
      (written : LeanExe.IR.ScalarStore.write locals destination value = some result) :
      Eval functions effects (.assign destination expression) world locals world result
  | seq (first : Eval functions effects a initial locals middle saved)
      (second : Eval functions effects b middle saved final result) :
      Eval functions effects (.seq a b) initial locals final result
  | yes (tested : condition.eval locals = some true)
      (body : Eval functions effects yes initial locals final result) :
      Eval functions effects (.branch condition yes no) initial locals final result
  | no (tested : condition.eval locals = some false)
      (body : Eval functions effects no initial locals final result) :
      Eval functions effects (.branch condition yes no) initial locals final result
  | done (tested : condition.eval locals = some false) :
      Eval functions effects (.loop condition body) world locals world locals
  | step (tested : condition.eval locals = some true)
      (body : Eval functions effects statement initial locals middle saved)
      (tail : Eval functions effects (.loop condition statement) middle saved final result) :
      Eval functions effects (.loop condition statement) initial locals final result
  | call (found : functions[callee]? = some function)
      (inputs : arguments expressions locals = some args)
      (arity : args.length = function.params)
      (body : Eval functions effects function.body initial
        (args ++ List.replicate function.locals 0) final returned)
      (output : function.result.eval returned = some value)
      (written : LeanExe.IR.ScalarStore.write locals destination value = some result) :
      Eval functions effects (.call destination callee expressions) initial locals final result
  | effect (inputs : arguments expressions locals = some args)
      (performed : effects operation args initial value final)
      (written : LeanExe.IR.ScalarStore.write locals destination value = some result) :
      Eval functions effects (.effect destination operation expressions) initial locals final result

theorem Eval.length {functions : Module} {effects : Effects σ}
    (execution : Eval functions effects statement initial locals final result) :
    result.length = locals.length := by
  induction execution with
  | skip | done => rfl
  | assign _ written | call _ _ _ _ _ written _ | effect _ _ written =>
      unfold LeanExe.IR.ScalarStore.write at written
      split at written
      · cases written; simp
      · contradiction
  | seq _ _ first second | step _ _ _ first second => exact second.trans first
  | yes _ _ ih | no _ _ ih => exact ih

/-- Successful invocation in source argument order. -/
def Invokes (functions : Module) (effects : Effects σ) (callee : Nat)
    (initial : σ) (args : List UInt64) (final : σ) (value : UInt64) : Prop :=
  ∃ function returned,
    functions[callee]? = some function ∧ args.length = function.params ∧
    Eval functions effects function.body initial
      (args ++ List.replicate function.locals 0) final returned ∧
    function.result.eval returned = some value

end LeanExe.Core
