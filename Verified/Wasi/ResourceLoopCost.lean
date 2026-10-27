import Verified.Wasi.ResourceCost
import LeanExe.Wasi.Prefix

namespace Verified.Wasi.Resource

def loopLive (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (live : Nat → Bool) (index : Nat) : Bool :=
  live index || test.uses (index + 2) || step.uses (index + 2)

def loopModes (stateMode : Mode) (modes : List Mode) : List Mode :=
  stateMode :: .borrowed :: modes.map (fun _ => .borrowed)

def loopEnv (env : Env context) (index : Nat) (state : type.denote) :
    Env (type :: .word :: context) :=
  .cons state (.cons (UInt64.ofNat index) env)

def loopResume (pure : PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) (remaining index : Nat) (state : type.denote) :
    LeanExe.Wasi.Action type.denote :=
  LeanExe.Wasi.resumeLoop
    (fun index state => test.denote pure.funs (.cons state (.cons index env)))
    (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
    LeanExe.Wasi.Action.pure remaining index state

def PureContext.loopCountCost (pure : PureContext pureSigs) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) : Nat :=
  pure.exprCost depth modes (fun index => loopLive test step live index || initial.uses index) count env

def PureContext.loopInitCost (pure : PureContext pureSigs) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) : Nat :=
  pure.loopCountCost depth modes live count initial test step env +
    pure.ownedCost depth modes (loopLive test step live) initial env

def PureContext.loopInitFits (pure : PureContext pureSigs) (depth : UInt64)
    (count : Expr pureSigs context .word) (initial : Expr pureSigs context type)
    (env : Env context) : Bool :=
  pure.exprFits depth count env && pure.exprFits depth initial env

def PureContext.loopTestCost (pure : PureContext pureSigs) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) (index : Nat) (state : type.denote) : Nat :=
  pure.exprCost depth (loopModes .borrowed modes)
    (fun sourceIndex => sourceIndex == 0 || shift 2 (loopLive test step live) sourceIndex)
    test (loopEnv env index state)

def PureContext.loopTestFits (pure : PureContext pureSigs) (depth : UInt64)
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (env : Env context) (index : Nat) (state : type.denote) : Bool :=
  pure.exprFits depth test (loopEnv env index state)

end Verified.Wasi.Resource
