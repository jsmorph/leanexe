import Verified.Wasi.Return
import Verified.Wasi.ReadCost

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

def PureContext.exprFits (context : PureContext signatures) (depth : UInt64)
    (value : Expr signatures sourceContext type) (env : Env sourceContext) : Bool :=
  value.fits context.funs (context.callFits depth) env

def PureContext.readCost (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (capacity : Expr signatures sourceContext .word)
    (env : Env sourceContext) : Nat :=
  context.exprCost depth modes live capacity env +
    Verified.Wasi.readCost (capacity.denote context.funs env)

def bindModes : ResultTy → List Mode → List Mode
  | .unit, modes => modes
  | .value _, modes => .owned :: modes

def bindLive (intermediate : ResultTy)
    (next : Command pureSigs effectSigs (intermediate.extend sourceContext) result)
    (live : Nat → Bool) (index : Nat) : Bool :=
  live index || next.uses (index + intermediate.bindCount)

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

theorem PureContext.readCost_zero (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (capacity : Expr signatures sourceContext .word)
    (env : Env sourceContext) (zero : capacity.denote context.funs env = 0) :
    context.readCost depth modes live capacity env = context.exprCost depth modes live capacity env := by
  rw [PureContext.readCost, zero, Verified.Wasi.readCost_zero, Nat.add_zero]

theorem PureContext.readCost_overflow (context : PureContext signatures) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (capacity : Expr signatures sourceContext .word)
    (env : Env sourceContext) (overflow : 4294967296 ≤ (capacity.denote context.funs env).toNat) :
    context.readCost depth modes live capacity env = context.exprCost depth modes live capacity env := by
  rw [PureContext.readCost, Verified.Wasi.readCost_overflow overflow, Nat.add_zero]

end Verified.Wasi.Resource
