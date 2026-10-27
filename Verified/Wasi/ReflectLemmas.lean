import Verified.Wasi.Source
import Verified.Wasi.Results
import LeanExe.Wasi.Related

namespace Verified.Wasi.Reflect

open LeanExe.Wasi LeanExe.Pipeline

def flattenAction (flatten : α → β) (action : Action α) : Action β :=
  Action.bind action fun value => .pure (flatten value)

theorem unit_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (value : Unit) :
    (Command.unit : Command pureSigs effectSigs context .unit).denote pureFuns effectFuns env =
      flattenAction (fun _ : Unit => ()) (.pure value) := rfl

theorem ret_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (expression : Expr pureSigs context type)
    (flatten : α → type.denote) (value : α)
    (hValue : expression.denote pureFuns env = flatten value) :
    (Command.ret expression).denote pureFuns effectFuns env =
      flattenAction flatten (.pure value) := by
  exact congrArg Action.pure hValue

theorem bind_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (first : Command pureSigs effectSigs context intermediate)
    (next : Command pureSigs effectSigs (intermediate.extend context) result)
    (firstNative : Action α) (nextNative : α → Action β)
    (firstFlat : α → intermediate.denote) (lastFlat : β → result.denote)
    (hFirst : first.denote pureFuns effectFuns env = flattenAction firstFlat firstNative)
    (hNext : ∀ value, next.denote pureFuns effectFuns
      (intermediate.bindEnv (firstFlat value) env) = flattenAction lastFlat (nextNative value)) :
    (Command.bind first next).denote pureFuns effectFuns env =
      flattenAction lastFlat (Action.bind firstNative nextNative) := by
  change Action.bind (first.denote pureFuns effectFuns env) _ = _
  rw [hFirst]
  unfold flattenAction
  rw [Action.bind_assoc, Action.bind_assoc]
  apply congrArg (Action.bind firstNative)
  funext value
  exact hNext value

theorem read_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (capacity : Expr pureSigs context .word) (value : UInt64)
    (hValue : capacity.denote pureFuns env = value) :
    (Command.read capacity).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : ReadResult → UInt64 × LeanExe.Bytes) (readSome value) := by
  rw [Command.denote, hValue]
  rfl

theorem write_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (output : Output) (bytes : Var context .bytes) (value : LeanExe.Bytes)
    (hValue : env.get bytes = value) :
    (Command.write output bytes).denote pureFuns effectFuns env =
      flattenAction (Flat.flat : WriteResult → UInt64 × UInt64)
        (match output with
        | .stdout => writeStdoutSome value
        | .stderr => writeStderrSome value) := by
  cases output <;> rw [Command.denote, hValue] <;> rfl

theorem write_value_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (output : Output) (bytes : Expr pureSigs context .bytes)
    (value : LeanExe.Bytes) (hValue : bytes.denote pureFuns env = value) :
    (Command.bind (Command.ret bytes) (Command.write output .here)).denote
      pureFuns effectFuns env =
      flattenAction (Flat.flat : WriteResult → UInt64 × UInt64)
        (match output with
        | .stdout => writeStdoutSome value
        | .stderr => writeStderrSome value) := by
  cases output <;>
    simp only [Command.denote, Action.bind, ResultTy.bindEnv, flattenAction,
      writeStdoutSome, writeStderrSome, hValue] <;> rfl

theorem exit_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (code : Expr pureSigs context .word) (value : UInt64)
    (flatten : α → result.denote) (hValue : code.denote pureFuns env = value) :
    (Command.exit code : Command pureSigs effectSigs context result).denote
      pureFuns effectFuns env = flattenAction flatten (.exit value) := by
  rw [Command.denote, hValue]
  rfl

theorem ite_eq (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (condition : Expr pureSigs context .bool)
    (yes no : Command pureSigs effectSigs context result)
    (value : Bool) (yesNative noNative : Action α) (flatten : α → result.denote)
    (hCondition : condition.denote pureFuns env = value)
    (hYes : yes.denote pureFuns effectFuns env = flattenAction flatten yesNative)
    (hNo : no.denote pureFuns effectFuns env = flattenAction flatten noNative) :
    (Command.ite condition yes no).denote pureFuns effectFuns env =
      flattenAction flatten (bif value then yesNative else noNative) := by
  rw [Command.denote, hCondition]
  cases value
  · exact hNo
  · exact hYes

theorem bind_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (first : Command pureSigs effectSigs context intermediate)
    (next : Command pureSigs effectSigs (intermediate.extend context) result)
    (firstNative : Action α) (nextNative : α → Action β)
    (firstFlat : α → intermediate.denote) (lastFlat : β → result.denote)
    (hFirst : Action.Rel (fun native flat => flat = firstFlat native)
      firstNative (first.denote pureFuns effectFuns env))
    (hNext : ∀ value, Action.Rel (fun native flat => flat = lastFlat native)
      (nextNative value) (next.denote pureFuns effectFuns
        (intermediate.bindEnv (firstFlat value) env))) :
    Action.Rel (fun native flat => flat = lastFlat native)
      (Action.bind firstNative nextNative) ((Command.bind first next).denote pureFuns effectFuns env) :=
  hFirst.bind fun native flat same => by cases same; exact hNext native

theorem ite_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (condition : Expr pureSigs context .bool)
    (yes no : Command pureSigs effectSigs context result)
    (value : Bool) (yesNative noNative : Action α) (flatten : α → result.denote)
    (hCondition : condition.denote pureFuns env = value)
    (hYes : Action.Rel (fun native flat => flat = flatten native)
      yesNative (yes.denote pureFuns effectFuns env))
    (hNo : Action.Rel (fun native flat => flat = flatten native)
      noNative (no.denote pureFuns effectFuns env)) :
    Action.Rel (fun native flat => flat = flatten native)
      (bif value then yesNative else noNative)
      ((Command.ite condition yes no).denote pureFuns effectFuns env) := by
  rw [Command.denote, hCondition]
  cases value
  · exact hNo
  · exact hYes

theorem ite_prop_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (condition : Expr pureSigs context .bool)
    (yes no : Command pureSigs effectSigs context result) (proposition : Prop)
    (decision : Decidable proposition) (yesNative noNative : Action α)
    (flatten : α → result.denote)
    (hCondition : condition.denote pureFuns env = @Decidable.decide proposition decision)
    (hYes : Action.Rel (fun native flat => flat = flatten native)
      yesNative (yes.denote pureFuns effectFuns env))
    (hNo : Action.Rel (fun native flat => flat = flatten native)
      noNative (no.denote pureFuns effectFuns env)) :
    Action.Rel (fun native flat => flat = flatten native)
      (@ite (Action α) proposition decision yesNative noNative)
      ((Command.ite condition yes no).denote pureFuns effectFuns env) := by
  rw [Command.denote, hCondition]
  cases decision with
  | isTrue _ => exact hYes
  | isFalse _ => exact hNo

theorem loop_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (countNative : UInt64) (initialNative : σ) (testNative : UInt64 → σ → Bool)
    (stepNative : UInt64 → σ → Action σ) (flatten : σ → type.denote)
    (hCount : count.denote pureFuns env = countNative)
    (hInitial : initial.denote pureFuns env = flatten initialNative)
    (hTest : ∀ index state, test.denote pureFuns (.cons (flatten state) (.cons index env)) =
      testNative index state)
    (hStep : ∀ index state, Action.Rel (fun native flat => flat = flatten native)
      (stepNative index state) (step.denote pureFuns effectFuns
        (.cons (flatten state) (.cons index env)))) :
    Action.Rel (fun native flat => flat = flatten native)
      (LeanExe.Wasi.loop countNative initialNative testNative stepNative)
      ((Command.loop count initial test step).denote pureFuns effectFuns env) := by
  rw [Command.denote, hCount, hInitial]
  refine .loop (states := fun native flat => flat = flatten native) countNative rfl ?_ ?_ ?_
  · intro index native flat same
    cases same
    exact (hTest index native).symm
  · intro index native flat same
    cases same
    exact hStep index native
  · intro native flat same
    exact .pure same

theorem call_rel (pureFuns : Funs pureSigs) (effectFuns : EffectFuns effectSigs)
    (env : Env context) (callee : EffectVar effectSigs signature)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i))
    (values : Env signature.params) (native : Action α) (flatten : α → signature.result.denote)
    (hArgs : Env.ofFn (fun i => (args i).denote pureFuns env) = values)
    (hCall : Action.Rel (fun native flat => flat = flatten native)
      native (effectFuns.get callee values)) :
    Action.Rel (fun native flat => flat = flatten native) native
      ((Command.call callee args).denote pureFuns effectFuns env) := by
  rw [Command.denote, hArgs]
  exact hCall

end Verified.Wasi.Reflect
