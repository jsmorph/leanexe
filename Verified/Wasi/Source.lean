import Verified.Source
import LeanExe.Wasi.Action

namespace Verified.Wasi

open LeanExe.Wasi

inductive ResultTy where
  | unit
  | value (type : Ty)

def ResultTy.denote : ResultTy → Type
  | .unit => Unit
  | .value type => type.denote

def ResultTy.extend : ResultTy → List Ty → List Ty
  | .unit, context => context
  | .value type, context => type :: context

def ResultTy.bindEnv {context : List Ty} : (result : ResultTy) → result.denote →
    Env context → Env (result.extend context)
  | .unit, _, env => env
  | .value _, payload, env => .cons payload env

structure EffectSig where
  name : String
  params : List Ty
  modes : List Mode
  result : ResultTy

inductive EffectVar : List EffectSig → EffectSig → Type where
  | here : EffectVar (signature :: signatures) signature
  | there : EffectVar signatures signature → EffectVar (other :: signatures) signature

def EffectVar.index : EffectVar signatures signature → Nat
  | .here (signatures := signatures) => signatures.length
  | .there callee => callee.index

inductive EffectFuns : List EffectSig → Type 1 where
  | nil : EffectFuns []
  | cons {signature : EffectSig} (function : Env signature.params → Action signature.result.denote)
      (rest : EffectFuns signatures) : EffectFuns (signature :: signatures)

def EffectFuns.get : EffectFuns signatures → EffectVar signatures signature →
    Env signature.params → Action signature.result.denote
  | .cons function _, .here => function
  | .cons _ rest, .there callee => rest.get callee

inductive Command (pureSigs : List Sig) (effectSigs : List EffectSig) :
    List Ty → ResultTy → Type where
  | unit : Command pureSigs effectSigs context .unit
  | ret (value : Expr pureSigs context type) :
      Command pureSigs effectSigs context (.value type)
  | bind (first : Command pureSigs effectSigs context intermediate)
      (next : Command pureSigs effectSigs (intermediate.extend context) result) :
      Command pureSigs effectSigs context result
  | ite (condition : Expr pureSigs context .bool)
      (yes no : Command pureSigs effectSigs context result) :
      Command pureSigs effectSigs context result
  | call (callee : EffectVar effectSigs signature)
      (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
      Command pureSigs effectSigs context signature.result
  | read (capacity : Expr pureSigs context .word) :
      Command pureSigs effectSigs context (.value (.pair .word .bytes))
  | write (output : Output) (bytes : Var context .bytes) :
      Command pureSigs effectSigs context (.value (.elem (.prod .word .word)))
  | exit (code : Expr pureSigs context .word) : Command pureSigs effectSigs context result
  | loop (count : Expr pureSigs context .word) (initial : Expr pureSigs context type)
      (test : Expr pureSigs (type :: .word :: context) .bool)
      (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) :
      Command pureSigs effectSigs context (.value type)

def Command.denote (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs) :
    {context : List Ty} → {result : ResultTy} → Command pureSigs effectSigs context result →
      Env context → Action result.denote
  | _, _, .unit, _ => .pure ()
  | _, _, .ret value, env => .pure (value.denote pureFuns env)
  | _, _, .bind (intermediate := intermediate) first next, env =>
      Action.bind (first.denote pureFuns effectFuns env) fun value =>
        next.denote pureFuns effectFuns (intermediate.bindEnv value env)
  | _, _, .ite condition yes no, env =>
      bif condition.denote pureFuns env then yes.denote pureFuns effectFuns env
        else no.denote pureFuns effectFuns env
  | _, _, .call callee args, env =>
      effectFuns.get callee (Env.ofFn fun i => (args i).denote pureFuns env)
  | _, _, .read capacity, env =>
      Action.bind (readSome (capacity.denote pureFuns env)) fun result =>
        .pure (result.errno, result.bytes)
  | _, _, .write output bytes, env =>
      Action.bind (match output with
        | .stdout => writeStdoutSome (env.get bytes)
        | .stderr => writeStderrSome (env.get bytes)) fun result =>
          .pure (result.errno, result.count)
  | _, _, .exit code, env => .exit (code.denote pureFuns env)
  | _, _, .loop count initial test step, env =>
      LeanExe.Wasi.loop (count.denote pureFuns env) (initial.denote pureFuns env)
        (fun index state => test.denote pureFuns (.cons state (.cons index env)))
        (fun index state => step.denote pureFuns effectFuns (.cons state (.cons index env)))

structure EffectFunc (pureSigs : List Sig) (effectSigs : List EffectSig) where
  name : String
  params : List Ty
  modes : List Mode
  result : ResultTy
  body : Command pureSigs effectSigs params result

def EffectFunc.sig (function : EffectFunc pureSigs effectSigs) : EffectSig :=
  ⟨function.name, function.params, function.modes, function.result⟩

inductive EffectProg (pureSigs : List Sig) : List EffectSig → Type where
  | nil : EffectProg pureSigs []
  | cons (function : EffectFunc pureSigs effectSigs) (rest : EffectProg pureSigs effectSigs) :
      EffectProg pureSigs (function.sig :: effectSigs)

def EffectProg.funs (pureFuns : Funs pureSigs) : EffectProg pureSigs effectSigs →
    EffectFuns effectSigs
  | .nil => .nil
  | .cons function rest => .cons (function.body.denote pureFuns (rest.funs pureFuns))
      (rest.funs pureFuns)

end Verified.Wasi
