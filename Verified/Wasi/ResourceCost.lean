module

public import Verified.Wasi.Return
public import Verified.Wasi.ReadAllCost

@[expose] public section

namespace Verified.Wasi.Resource

open Wasm LeanExe.Pipeline LeanExe.Runtime

structure PureContext (signatures : List Sig) where
  funs : Funs signatures
  flags : Flags signatures
  bounds : Nat → Bounds signatures
  fits : Nat → Fits signatures

def PureContext.ofProg (program : Prog signatures) (funs : Funs signatures) :
    PureContext signatures :=
  ⟨funs, program.flags, program.boundsAt funs, program.fitsAt funs⟩

def PureContext.callBounds (context : PureContext signatures) (depth : UInt64) : Bounds signatures :=
  context.bounds (framesAt (depth + 1))

def PureContext.callFits (context : PureContext signatures) (depth : UInt64) : Fits signatures :=
  context.fits (framesAt (depth + 1))

def entryFits (depth : UInt64) : Bool := decide (depth < depthLimit)

def PureContext.exprCost (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (value : Expr signatures sourceContext type)
    (env : Env sourceContext) : Nat :=
  value.allocs context.funs context.flags (context.callBounds depth) modes [] live env

def PureContext.ownedCost (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (value : Expr signatures sourceContext type)
    (env : Env sourceContext) : Nat :=
  context.exprCost depth modes live value env +
    coerceCost type (value.mode modes) .owned (value.denote context.funs env)

/-- The charge of a `sys` command before its call: the charge of the take of its buffer, when it
has one, which copies a buffer that stays live or that it borrows. -/
def PureContext.sysTakeCost (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (args : List (Var sourceContext .word))
    (inputs buffers : List (Var sourceContext .bytes)) (env : Env sourceContext) : Nat :=
  match buffers with
  | [] => 0
  | buffer :: _ => context.ownedCost depth modes (sysTakeLive live args inputs) (Expr.var buffer) env

def PureContext.exprFits (context : PureContext signatures) (depth : UInt64)
    (value : Expr signatures sourceContext type) (env : Env sourceContext) : Bool :=
  value.fits context.funs (context.callFits depth) env

def PureContext.readAllCost (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (limit : Expr signatures sourceContext .word)
    (env : Env sourceContext) : Nat :=
  context.exprCost depth modes live limit env +
    Verified.Wasi.readAllCost (limit.denote context.funs env)

def bindModes : ResultTy → List Mode → List Mode
  | .unit, modes => modes
  | .value _, modes => .owned :: modes

def bindLive (intermediate : ResultTy)
    (next : Command pureSigs effectSigs (intermediate.extend sourceContext) result)
    (live : Nat → Bool) (index : Nat) : Bool :=
  live index || next.uses (index + intermediate.bindCount)

/-- The modes of the context of a `letPair`'s body: each component has the mode of the pair. -/
def letPairModes (pair : Var sourceContext (.pair first second)) (modes : List Mode) : List Mode :=
  modeAt modes pair.index :: modeAt modes pair.index :: modes

/-- The environment of a `letPair`'s body: the pair's second component as variable 0 and its first
as variable 1. -/
def letPairEnv (pair : Var sourceContext (.pair first second)) (env : Env sourceContext) :
    Env (second :: first :: sourceContext) :=
  .cons (env.get pair).2 (.cons (env.get pair).1 env)

/-- The charge of a `letPair` before its body: the copy of an owned pair that stays live. -/
def letPairCost (modes : List Mode) (live : Nat → Bool)
    (pair : Var sourceContext (.pair first second))
    (body : Command pureSigs effectSigs (second :: first :: sourceContext) result)
    (env : Env sourceContext) : Nat :=
  pair.cost modes (fun i => live i || body.uses (i + 2)) (env.get pair)

theorem letPairCost_borrowed {modes : List Mode} {live : Nat → Bool}
    {pair : Var sourceContext (.pair first second)}
    {body : Command pureSigs effectSigs (second :: first :: sourceContext) result}
    {env : Env sourceContext} (borrowed : modeAt modes pair.index = .borrowed) :
    letPairCost modes live pair body env = 0 := by
  simp [letPairCost, Var.cost, borrowed]

theorem letPairCost_dead {modes : List Mode} {live : Nat → Bool}
    {pair : Var sourceContext (.pair first second)}
    {body : Command pureSigs effectSigs (second :: first :: sourceContext) result}
    {env : Env sourceContext} (dead : (live pair.index || body.uses (pair.index + 2)) = false) :
    letPairCost modes live pair body env = 0 := by
  simp [letPairCost, Var.cost, dead]

def argumentMoves (signature : EffectSig) (modes : List Mode) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs sourceContext (signature.params.get i))
    (index : Fin signature.params.length) : Bool :=
  signature.mode index == .owned &&
    match (args index).varIndex? with
    | some sourceIndex => modeAt modes sourceIndex == .owned && !live sourceIndex &&
        !(argsAny fun other => other != index && !(signature.params.get other).scalar &&
          (args other).uses sourceIndex)
    | none => false

def argumentLive {signature : EffectSig}
    (args : (i : Fin signature.params.length) → Expr pureSigs sourceContext (signature.params.get i))
    (live : Nat → Bool) (index : Nat) : Bool :=
  live index || argsAny fun arg => (args arg).uses index

def argumentKept (signature : EffectSig) (modes : List Mode) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs sourceContext (signature.params.get i))
    (index : Nat) : Bool :=
  argumentLive args live index &&
    !(argsAny fun arg => argumentMoves signature modes live args arg && (args arg).uses index)

def PureContext.argumentCost (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (signature : EffectSig)
    (args : (i : Fin signature.params.length) → Expr signatures sourceContext (signature.params.get i))
    (env : Env sourceContext) : Nat :=
  argsSum fun index =>
    if (signature.params.get index).scalar then
      context.exprCost depth modes (argumentLive args live) (args index) env
    else if signature.mode index = .owned then
      (args index).ownedCost modes (argumentKept signature modes live args) env
    else 0

def PureContext.argumentFits (context : PureContext signatures) (depth : UInt64)
    {signature : EffectSig}
    (args : (i : Fin signature.params.length) → Expr signatures sourceContext (signature.params.get i))
    (env : Env sourceContext) : Bool :=
  argsAll fun index => context.exprFits depth (args index) env

theorem PureContext.returnCost_nil (context : PureContext signatures) (depth : UInt64)
    (value : Expr signatures sourceContext type) (env : Env sourceContext) (slots : List Slot)
    (live : Nat → Bool) (store : Store Unit) (locals : Locals) :
    Verified.Wasi.returnCost context.funs context.flags (context.callBounds depth)
      value env slots [] live store locals =
      context.ownedCost depth (slots.map Slot.mode) live value env := by
  simp only [Verified.Wasi.returnCost, dyingPot_nil, Nat.zero_add,
    PureContext.ownedCost, PureContext.exprCost]

end Verified.Wasi.Resource
