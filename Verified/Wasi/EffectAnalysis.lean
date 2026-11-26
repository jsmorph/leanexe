module

public import Verified.Wasi.Source
public import Verified.CodeMask

@[expose] public section

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
satisfy the same requirements. -/
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
  | _, _, .read buffer start count, index =>
    index == buffer.index || (index == start.index || index == count.index)
  | _, _, .readAll limit, index => limit.uses index
  | _, _, .write _ buffer start count, index =>
    index == buffer.index || (index == start.index || index == count.index)
  | _, _, .exit code, index => code.uses index
  | _, _, .loop count initial test step, index =>
    count.uses index || initial.uses index || test.uses (index + 2) || step.uses (index + 2)
  | _, _, .sys _ _ args inputs buffers, index =>
    (buffers.any fun buffer => index == buffer.index) ||
      ((inputs.any fun input => index == input.index) || args.any fun arg => index == arg.index)
  | _, _, .letPair pair body, index => index == pair.index || body.uses (index + 2)

/-- The variables of a list as a bitmask, whose bit `i` is set when variable `i` is in the
list. -/
def varsMask : List (Var context type) → Nat
  | [] => 0
  | var :: rest => 1 <<< var.index ||| varsMask rest

/-- The variables that a command reads, as a bitmask whose bit `i` is set when it reads variable
`i`: `Command.uses` as data.  The kernel evaluates the code generator in each program's byte
theorems, and the generator learns the variables live after each command from these masks, each
computed once from those of the command's parts, where `Command.uses` walks the rest of the
program for each variable that it is asked about. -/
def Command.useMask : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Nat
  | _, _, .unit => 0
  | _, _, .ret value => value.useMask
  | _, _, .bind (intermediate := intermediate) first next =>
    first.useMask ||| next.useMask >>> intermediate.bindCount
  | _, _, .ite condition yes no => condition.useMask ||| yes.useMask ||| no.useMask
  | _, _, .call _ args => argsMask fun i => (args i).useMask
  | _, _, .read buffer start count =>
    1 <<< buffer.index ||| (1 <<< start.index ||| 1 <<< count.index)
  | _, _, .readAll limit => limit.useMask
  | _, _, .write _ buffer start count =>
    1 <<< buffer.index ||| (1 <<< start.index ||| 1 <<< count.index)
  | _, _, .exit code => code.useMask
  | _, _, .loop count initial test step =>
    count.useMask ||| initial.useMask ||| test.useMask >>> 2 ||| step.useMask >>> 2
  | _, _, .sys _ _ args inputs buffers => varsMask buffers ||| (varsMask inputs ||| varsMask args)
  | _, _, .letPair pair body => 1 <<< pair.index ||| body.useMask >>> 2

theorem _root_.Verified.Expr.useMask_testBit {Γ : List Ty} {t : Ty} (e : Expr pureSigs Γ t)
    (i : Nat) : e.useMask.testBit i = e.uses i :=
  Expr.usesFast_eq e i

theorem varsMask_testBit (vars : List (Var context type)) (i : Nat) :
    (varsMask vars).testBit i = vars.any fun var => i == var.index := by
  induction vars with
  | nil => simp [varsMask]
  | cons var rest ih =>
    simp only [varsMask, Nat.testBit_or, testBit_one_shiftLeft, ih, List.any_cons]

theorem Command.useMask_testBit (command : Command pureSigs effectSigs context result) (i : Nat) :
    command.useMask.testBit i = command.uses i := by
  induction command generalizing i with
  | unit => simp [Command.useMask, Command.uses]
  | ret value => exact value.useMask_testBit i
  | bind first next firstIh nextIh =>
    simp only [Command.useMask, Command.uses, Nat.testBit_or, Nat.testBit_shiftRight, firstIh,
      nextIh, Nat.add_comm]
  | ite condition yes no yesIh noIh =>
    simp only [Command.useMask, Command.uses, Nat.testBit_or, Expr.useMask_testBit, yesIh, noIh]
  | call callee args =>
    simp only [Command.useMask, Command.uses, argsMask_testBit, Expr.useMask_testBit]
  | read buffer start count | write output buffer start count =>
    simp only [Command.useMask, Command.uses, Nat.testBit_or, testBit_one_shiftLeft]
  | readAll limit => exact limit.useMask_testBit i
  | exit code => exact code.useMask_testBit i
  | loop count initial test step stepIh =>
    simp only [Command.useMask, Command.uses, Nat.testBit_or, Nat.testBit_shiftRight,
      Expr.useMask_testBit, stepIh, Nat.add_comm]
  | sys call form args inputs buffers =>
    simp only [Command.useMask, Command.uses, Nat.testBit_or, varsMask_testBit]
  | letPair pair body bodyIh =>
    simp only [Command.useMask, Command.uses, Nat.testBit_or, Nat.testBit_shiftRight,
      testBit_one_shiftLeft, bodyIh, Nat.add_comm]

theorem testBit_varsMask_eq (vars : List (Var context type)) :
    Nat.testBit (varsMask vars) = fun i => vars.any fun var => i == var.index :=
  funext (varsMask_testBit vars)

/-- The bits of a list's mask past a bound variable, as the release after a `sys` command with a
buffer tests them. -/
theorem testBit_varsMask_shiftLeft_one_eq (vars : List (Var context type)) :
    Nat.testBit (varsMask vars <<< 1) = fun i => vars.any fun var => i == var.index + 1 := by
  funext i
  rw [testBit_shiftLeft_eq, shift]
  cases i with
  | zero => simp
  | succ i => simp [varsMask_testBit]

/-- The variables live after the take of a `sys` command's buffer: those live after the command,
and its inputs and word arguments, which the call reads. -/
def sysTakeLive (live : Nat → Bool) (args : List (Var context .word))
    (inputs : List (Var context .bytes)) (i : Nat) : Bool :=
  live i || ((inputs.any fun input => i == input.index) || args.any fun arg => i == arg.index)

def Command.literals : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → List Bytes.Literal
  | _, _, .unit | _, _, .read _ _ _ | _, _, .write _ _ _ _ | _, _, .sys _ _ _ _ _ => []
  | _, _, .ret value => value.literals
  | _, _, .bind first next => first.literals ++ next.literals
  | _, _, .ite condition yes no => condition.literals ++ yes.literals ++ no.literals
  | _, _, .call _ args => (List.ofFn fun i => (args i).literals).flatten
  | _, _, .readAll limit => limit.literals
  | _, _, .exit code => code.literals
  | _, _, .loop count initial test step =>
    count.literals ++ initial.literals ++ test.literals ++ step.literals
  | _, _, .letPair _ body => body.literals

def Command.Covered (command : Command pureSigs effectSigs context result)
    (pool : Bytes.LiteralPool) : Prop := command.literals ⊆ pool.values

def Command.placeArgs : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Bool
  | _, _, .unit | _, _, .read _ _ _ | _, _, .write _ _ _ _ | _, _, .sys _ _ _ _ _ => true
  | _, _, .ret value => value.placeArgs
  | _, _, .bind first next => first.placeArgs && next.placeArgs
  | _, _, .ite condition yes no => condition.placeArgs && yes.placeArgs && no.placeArgs
  | _, _, .call (signature := signature) _ args => signature.placeArgs args
  | _, _, .readAll limit => limit.placeArgs
  | _, _, .exit code => code.placeArgs
  | _, _, .loop count initial test step =>
    count.placeArgs && initial.placeArgs && test.placeArgs && step.placeArgs
  | _, _, .letPair _ body => body.placeArgs

/-- Whether each `sys` command has a call that the compiler supports, in its form, with the word
arguments of `Call.argWords`, one input variable for each input parameter, one buffer variable for
each parameter that fills a buffer, and whether `calls` holds the calls that its code uses. -/
def Command.callsReady (calls : List LeanExe.Wasi.Call) : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Bool
  | _, _, .bind first next => first.callsReady calls && next.callsReady calls
  | _, _, .ite _ yes no => yes.callsReady calls && no.callsReady calls
  | _, _, .loop _ _ _ step => step.callsReady calls
  | _, _, .letPair _ body => body.callsReady calls
  | _, _, .sys operation form args inputs buffers =>
    operation.compiled && operation.form == form && args.length == operation.argWords &&
      inputs.length == operation.inputCount && buffers.length == operation.bufferCount &&
      operation.uses.all calls.contains
  | _, _, .unit | _, _, .ret _ | _, _, .call _ _ | _, _, .read _ _ _ | _, _, .readAll _
  | _, _, .write _ _ _ _ | _, _, .exit _ => true

/-- The calls that the `sys` commands of a command use, in order, with repetitions. -/
def Command.callsUsed : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → List LeanExe.Wasi.Call
  | _, _, .bind first next => first.callsUsed ++ next.callsUsed
  | _, _, .ite _ yes no => yes.callsUsed ++ no.callsUsed
  | _, _, .loop _ _ _ step => step.callsUsed
  | _, _, .letPair _ body => body.callsUsed
  | _, _, .sys operation _ _ _ _ => operation.uses
  | _, _, .unit | _, _, .ret _ | _, _, .call _ _ | _, _, .read _ _ _ | _, _, .readAll _
  | _, _, .write _ _ _ _ | _, _, .exit _ => []

/-- The calls that the `sys` commands of a program use, each once, in order of first use. -/
def EffectProg.callsUsed : {effectSigs : List EffectSig} →
    EffectProg pureSigs effectSigs → List LeanExe.Wasi.Call
  | _, .nil => []
  | _, .cons function rest => (rest.callsUsed ++ function.body.callsUsed).eraseDups

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

theorem Command.covered_letPair (pair : Var context (.pair first second))
    (body : Command pureSigs effectSigs (second :: first :: context) result)
    (pool : Bytes.LiteralPool) :
    (Command.letPair pair body).Covered pool ↔ body.Covered pool := Iff.rfl

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
