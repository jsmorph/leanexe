import Project.Correct.Scalar64.Expression

/-!
The certified path uses a scalar IR with explicit local assignment, structured
control, and direct calls. Expression evaluation is strict and includes scratch
writes. It has no memory/global/import operations or hidden failure defaults.
The independent source machine remains in LeanExe.Correct.Scalar64.
-/
namespace Project.Correct.Scalar64
open Wasm
open Project.ProofKit.ScalarTransition

inductive Command where
  | skip
  | assign (index : Nat) (value : Expr .u64)
  | seq (first second : Command)
  | branch (condition : Expr .bool) (yes no : Command)
  | loop (condition : Expr .bool) (body : Command)
  | call (destination function : Nat) (arguments : List (Expr .u64))
  deriving Repr

def lowerArgs (scratch : Nat) : List (Expr .u64) → Wasm.Program
  | [] => []
  | expression :: rest => expression.lower scratch ++ lowerArgs scratch rest

def evalArgs (scratch : Nat) : List (Expr .u64) → State → Option (List UInt64 × State)
  | [], state => some ([], state)
  | expression :: rest, state => do
      let (value, afterExpression) ← expression.eval scratch state
      let (values, final) ← evalArgs scratch rest afterExpression
      pure (value :: values, final)

def Command.lower (scratch : Nat) : Command → Wasm.Program
  | .skip => []
  | .assign index expression => expression.lower scratch ++ [.localSet index]
  | .seq first second => first.lower scratch ++ second.lower scratch
  | .branch condition yes no =>
      condition.lower scratch ++ [.iff 0 0 (yes.lower scratch) (no.lower scratch)]
  | .loop condition body => [.block 0 0 [.loop 0 0
      (condition.lower scratch ++ [.eqz, .br_if 1] ++ body.lower scratch ++ [.br 0])]]
  | .call destination function arguments =>
      lowerArgs scratch arguments ++ [.call function, .localSet destination]

structure Function where
  arity : Nat
  localCount : Nat
  scratch : Nat
  body : Command
  result : Expr .u64
  deriving Repr

def Function.initial (function : Function) (args : List UInt64) : State :=
  { params := args.map Value.i64, locals := List.replicate function.localCount (.i64 0) }

def Function.lower (function : Function) (index : Nat) : Wasm.Function :=
  { params := List.replicate function.arity .i64
    locals := List.replicate function.localCount .i64
    results := [.i64]
    body := function.body.lower function.scratch ++ function.result.lower function.scratch
    typeIdx := some index }

/-- Declarative total execution. The loop rule supplies a decreasing invariant;
    its premise executes the body in this IR, without mentioning WASM code. -/
inductive Executes (functions : List Function) :
    Nat → Command → State → State → Prop where
  | skip : Executes functions scratch .skip state state
  | assign (valueRun : expression.eval scratch state = some (value, afterValue))
      (write : afterValue.set? index (.i64 value) = some final) :
      Executes functions scratch (.assign index expression) state final
  | seq (firstRun : Executes functions scratch first initial middle)
      (secondRun : Executes functions scratch second middle final) :
      Executes functions scratch (.seq first second) initial final
  | branch (conditionRun : condition.eval scratch initial = some (choice, afterCondition))
      (bodyRun : Executes functions scratch (if choice then yes else no) afterCondition final) :
      Executes functions scratch (.branch condition yes no) initial final
  | loop (Inv : State → Prop) (measure : State → Nat)
      (choice : State → Bool) (afterCondition afterBody : State → State)
      (init : Inv initial)
      (conditionRun : ∀ current, Inv current →
        condition.eval scratch current = some (choice current, afterCondition current))
      (bodyRun : ∀ current, Inv current → choice current = true →
        Executes functions scratch body (afterCondition current) (afterBody current))
      (invariant : ∀ current, Inv current → choice current = true → Inv (afterBody current))
      (decreases : ∀ current, Inv current → choice current = true →
        measure (afterBody current) < measure current)
      (exit : ∀ current, Inv current → choice current = false → afterCondition current = final) :
      Executes functions scratch (.loop condition body) initial final
  | call (argumentsRun : evalArgs scratch arguments initial = some (args, afterArgs))
      (found : functions[index]? = some function) (arity : args.length = function.arity)
      (bodyRun : Executes functions function.scratch function.body (function.initial args) afterBody)
      (resultRun : function.result.eval function.scratch afterBody = some (result, afterResult))
      (write : afterArgs.set? destination (.i64 result) = some final) :
      Executes functions scratch (.call destination index arguments) initial final

end Project.Correct.Scalar64
