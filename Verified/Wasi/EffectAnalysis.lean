import Verified.Wasi.Source
import Verified.Compile

namespace Verified.Wasi

def ResultTy.width : ResultTy → Nat
  | .unit => 0
  | .value type => type.width

def ResultTy.types : ResultTy → List Wasm.ValueType
  | .unit => []
  | .value type => type.types

def ResultTy.scalar : ResultTy → Bool
  | .unit => true
  | .value type => type.scalar

def ResultTy.bindCount : ResultTy → Nat
  | .unit => 0
  | .value _ => 1

theorem ResultTy.extend_length (result : ResultTy) (context : List Ty) :
    (result.extend context).length = result.bindCount + context.length := by
  cases result <;> simp only [ResultTy.extend, ResultTy.bindCount, List.length_cons] <;> omega

def EffectSig.mode (signature : EffectSig) : Nat → Mode :=
  paramMode signature.params signature.modes

/-- Heap-valued arguments are places, owned arguments are variables, and nested pure calls
obey the same requirements. -/
def EffectSig.placeArgs (signature : EffectSig)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
    Bool :=
  argsAny (fun i => !(signature.params.get i).scalar && !(args i).isPlace) == false &&
    argsAny (fun i => signature.mode i == .owned && (args i).varIndex?.isNone) == false &&
    !(argsAny fun i => !(args i).placeArgs)

def Command.uses : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Nat → Bool
  | _, _, .unit, _ => false
  | _, _, .ret value, index => value.uses index
  | _, _, .bind (intermediate := intermediate) first next, index =>
    first.uses index || next.uses (index + intermediate.bindCount)
  | _, _, .ite condition yes no, index =>
    condition.uses index || yes.uses index || no.uses index
  | _, _, .call _ args, index => argsAny fun i => (args i).uses index
  | _, _, .read capacity, index => capacity.uses index
  | _, _, .write _ bytes, index => index == bytes.index
  | _, _, .exit code, index => code.uses index
  | _, _, .loop count initial test step, index =>
    count.uses index || initial.uses index || test.uses (index + 2) || step.uses (index + 2)

def Command.literals : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → List Bytes.Literal
  | _, _, .unit | _, _, .write _ _ => []
  | _, _, .ret value => value.literals
  | _, _, .bind first next => first.literals ++ next.literals
  | _, _, .ite condition yes no => condition.literals ++ yes.literals ++ no.literals
  | _, _, .call _ args => (List.ofFn fun i => (args i).literals).flatten
  | _, _, .read capacity => capacity.literals
  | _, _, .exit code => code.literals
  | _, _, .loop count initial test step =>
    count.literals ++ initial.literals ++ test.literals ++ step.literals

def Command.Covered (command : Command pureSigs effectSigs context result)
    (pool : Bytes.LiteralPool) : Prop := command.literals ⊆ pool.values

def Command.placeArgs : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Bool
  | _, _, .unit | _, _, .write _ _ => true
  | _, _, .ret value => value.placeArgs
  | _, _, .bind first next => first.placeArgs && next.placeArgs
  | _, _, .ite condition yes no => condition.placeArgs && yes.placeArgs && no.placeArgs
  | _, _, .call (signature := signature) _ args => signature.placeArgs args
  | _, _, .read capacity => capacity.placeArgs
  | _, _, .exit code => code.placeArgs
  | _, _, .loop count initial test step =>
    count.placeArgs && initial.placeArgs && test.placeArgs && step.placeArgs

def EffectProg.literals : {effectSigs : List EffectSig} →
    EffectProg pureSigs effectSigs → List Bytes.Literal
  | _, .nil => []
  | _, .cons function rest => rest.literals ++ function.body.literals

def EffectProg.Covered (program : EffectProg pureSigs effectSigs) (pool : Bytes.LiteralPool) :
    Prop := program.literals ⊆ pool.values

theorem Command.uses_bind_unit
    (first : Command pureSigs effectSigs context .unit)
    (next : Command pureSigs effectSigs context result) (index : Nat) :
    (Command.bind first next).uses index = (first.uses index || next.uses index) := rfl

theorem Command.uses_bind_value
    (first : Command pureSigs effectSigs context (.value type))
    (next : Command pureSigs effectSigs (type :: context) result) (index : Nat) :
    (Command.bind first next).uses index = (first.uses index || next.uses (index + 1)) := rfl

theorem Command.covered_bind
    (first : Command pureSigs effectSigs context intermediate)
    (next : Command pureSigs effectSigs (intermediate.extend context) result)
    (pool : Bytes.LiteralPool) :
    (Command.bind first next).Covered pool ↔ first.Covered pool ∧ next.Covered pool := by
  simp only [Command.Covered, Command.literals, List.append_subset]

theorem Command.covered_ite (condition : Expr pureSigs context .bool)
    (yes no : Command pureSigs effectSigs context result) (pool : Bytes.LiteralPool) :
    (Command.ite condition yes no).Covered pool ↔
      condition.Covered pool ∧ yes.Covered pool ∧ no.Covered pool := by
  simp only [Command.Covered, Command.literals, Expr.Covered, List.append_subset, and_assoc]

theorem Command.covered_call (callee : EffectVar effectSigs signature)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i))
    (pool : Bytes.LiteralPool) :
    (Command.call callee args).Covered pool ↔ ∀ i, (args i).Covered pool := by
  simpa only [Command.Covered, Command.literals, Expr.Covered] using
    (literals_args_subset (args := fun i => (args i).literals) (values := pool.values))

theorem Command.covered_loop (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (pool : Bytes.LiteralPool) :
    (Command.loop count initial test step).Covered pool ↔
      count.Covered pool ∧ initial.Covered pool ∧ test.Covered pool ∧ step.Covered pool := by
  simp only [Command.Covered, Command.literals, Expr.Covered, List.append_subset, and_assoc]

theorem EffectProg.covered_cons (function : EffectFunc pureSigs effectSigs)
    (rest : EffectProg pureSigs effectSigs) (pool : Bytes.LiteralPool) :
    (EffectProg.cons function rest).Covered pool ↔
      rest.Covered pool ∧ function.body.Covered pool := by
  simp only [EffectProg.Covered, EffectProg.literals, Command.Covered, List.append_subset]

end Verified.Wasi
