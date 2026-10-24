import Verified.Wasi.ResourceLoopCost
import LeanExe.Wasi.Semantics

namespace Verified.Wasi.Resource

open LeanExe.Wasi

mutual

inductive ResourceExec {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    (depth : UInt64) → (modes : List Mode) → (live : Nat → Bool) →
    {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Env context →
    World → List Event → Outcome result.denote → World → Nat → Bool → Prop where
  | unit (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
      (live : Nat → Bool) (env : Env context) (world : World) :
      ResourceExec host pure program depth modes live .unit env world [] (.returned ()) world 0 true
  | ret (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
      (live : Nat → Bool) (value : Expr pureSigs context type) (env : Env context) (world : World) :
      ResourceExec host pure program depth modes live (.ret value) env world []
        (.returned (value.denote pure.funs env)) world
        (pure.ownedCost depth modes live value env) (pure.exprFits depth value env)
  | read (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
      (live : Nat → Bool) (capacity : Expr pureSigs context .word) (env : Env context)
      (execution : Exec host ((Command.read capacity).denote pure.funs (program.funs pure.funs) env)
        world trace outcome final) :
      ResourceExec host pure program depth modes live (.read capacity) env world trace outcome final
        (pure.readCost depth modes live capacity env) (pure.exprFits depth capacity env)
  | write {program : EffectProg pureSigs effectSigs}
      {output : Output} {bytes : Var context .bytes} {env : Env context}
      (execution : Exec host ((Command.write output bytes).denote pure.funs (program.funs pure.funs) env)
        world trace outcome final) :
      ResourceExec host pure program depth modes live (.write output bytes) env
        world trace outcome final 0 true
  | exit {program : EffectProg pureSigs effectSigs}
      {code : Expr pureSigs context .word} {env : Env context}
      (execution : Exec host ((Command.exit code : Command pureSigs effectSigs context result).denote
        pure.funs (program.funs pure.funs) env) world trace outcome final) :
      ResourceExec host pure program depth modes live (.exit code) env world trace outcome final
        (pure.exprCost depth modes live code env) (pure.exprFits depth code env)
  | bind_return {program : EffectProg pureSigs effectSigs}
      {first : Command pureSigs effectSigs context intermediate}
      {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
      (firstRun : ResourceExec host pure program depth modes (bindLive intermediate next live)
        first env world firstTrace (.returned value) after firstSpent firstFits)
      (nextRun : ResourceExec host pure program depth (bindModes intermediate modes)
        (shift intermediate.bindCount live) next (intermediate.bindEnv value env)
        after rest outcome final nextSpent nextFits) :
      ResourceExec host pure program depth modes live (.bind first next) env
        world (firstTrace ++ rest) outcome final (firstSpent + nextSpent) (firstFits && nextFits)
  | bind_exit {program : EffectProg pureSigs effectSigs}
      {first : Command pureSigs effectSigs context intermediate}
      {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
      (firstRun : ResourceExec host pure program depth modes (bindLive intermediate next live)
        first env world trace (.exited code) final spent fits) :
      ResourceExec host pure program depth modes live (.bind first next) env
        world trace (.exited code) final spent fits
  | bind_trap {program : EffectProg pureSigs effectSigs}
      {first : Command pureSigs effectSigs context intermediate}
      {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
      (firstRun : ResourceExec host pure program depth modes (bindLive intermediate next live)
        first env world trace (.trapped message) final spent fits) :
      ResourceExec host pure program depth modes live (.bind first next) env
        world trace (.trapped message) final spent fits
  | ite_yes {program : EffectProg pureSigs effectSigs}
      {condition : Expr pureSigs context .bool}
      {yes no : Command pureSigs effectSigs context result} {env : Env context}
      (chosen : condition.denote pure.funs env = true)
      (execution : ResourceExec host pure program depth modes live yes env world trace outcome final spent fits) :
      ResourceExec host pure program depth modes live (.ite condition yes no) env
        world trace outcome final
        (pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env + spent)
        (pure.exprFits depth condition env && fits)
  | ite_no {program : EffectProg pureSigs effectSigs}
      {condition : Expr pureSigs context .bool}
      {yes no : Command pureSigs effectSigs context result} {env : Env context}
      (chosen : condition.denote pure.funs env = false)
      (execution : ResourceExec host pure program depth modes live no env world trace outcome final spent fits) :
      ResourceExec host pure program depth modes live (.ite condition yes no) env
        world trace outcome final
        (pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env + spent)
        (pure.exprFits depth condition env && fits)
  | call {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
      {args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)}
      {env : Env context}
      (execution : ResourceCall host pure program callee (depth + 1)
        (Env.ofFn fun i => (args i).denote pure.funs env) world trace outcome final spent fits) :
      ResourceExec host pure program depth modes live (.call callee args) env
        world trace outcome final
        (pure.argumentCost depth modes live signature args env + spent)
        (pure.argumentFits depth args env && fits)
  | loop {program : EffectProg pureSigs effectSigs}
      {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      (execution : ResourceLoopExec host pure program depth modes live test step env
        (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env)
        world trace outcome final spent fits) :
      ResourceExec host pure program depth modes live (.loop count initial test step) env
        world trace outcome final
        (pure.loopInitCost depth modes live count initial test step env + spent)
        (pure.loopInitFits depth count initial env && fits)

inductive ResourceCall {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    {signature : EffectSig} → EffectVar effectSigs signature → UInt64 → Env signature.params →
    World → List Event → Outcome signature.result.denote → World → Nat → Bool → Prop where
  | here {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
      {env : Env function.params}
      {outcome : Outcome function.result.denote}
      (execution : ResourceExec host pure rest depth (entryModes function.params function.modes)
        (fun _ => false) function.body env world trace outcome final spent fits) :
      ResourceCall host pure (.cons function rest) .here depth env world trace outcome final spent
        (entryFits depth && fits)
  | there {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
      {callee : EffectVar effectSigs signature} {env : Env signature.params}
      (execution : ResourceCall host pure rest callee depth env world trace outcome final spent fits) :
      ResourceCall host pure (.cons function rest) (.there callee) depth env
        world trace outcome final spent fits

inductive ResourceLoopExec {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    UInt64 → List Mode → (Nat → Bool) → {context : List Ty} → {type : Ty} →
    (test : Expr pureSigs (type :: .word :: context) .bool) →
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) → Env context →
    Nat → Nat → type.denote →
    World → List Event → Outcome type.denote → World → Nat → Bool → Prop where
  | zero {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
      {env : Env context} (world : World) (index : Nat) (state : type.denote) :
      ResourceLoopExec host pure program depth modes live test step env 0 index state
        world [] (.returned state) world 0 true
  | stop {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state : type.denote} (world : World)
      (chosen : test.denote pure.funs (loopEnv env index state) = false) :
      ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index state
        world [] (.returned state) world
        (pure.loopTestCost depth modes live test step env index state)
        (pure.loopTestFits depth test env index state)
  | next {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state nextState : type.denote}
      (chosen : test.denote pure.funs (loopEnv env index state) = true)
      (stepRun : ResourceExec host pure program depth (loopModes .owned modes)
        (shift 2 (loopLive test step live)) step (loopEnv env index state)
        world firstTrace (.returned nextState) after stepSpent stepFits)
      (restRun : ResourceLoopExec host pure program depth modes live test step env
        remaining (index + 1) nextState after restTrace outcome final restSpent restFits) :
      ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index state
        world (firstTrace ++ restTrace) outcome final
        (pure.loopTestCost depth modes live test step env index state + stepSpent + restSpent)
        (pure.loopTestFits depth test env index state && stepFits && restFits)
  | exit {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state : type.denote}
      (chosen : test.denote pure.funs (loopEnv env index state) = true)
      (stepRun : ResourceExec host pure program depth (loopModes .owned modes)
        (shift 2 (loopLive test step live)) step (loopEnv env index state)
        world trace (.exited code) final spent fits) :
      ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index state
        world trace (.exited code) final
        (pure.loopTestCost depth modes live test step env index state + spent)
        (pure.loopTestFits depth test env index state && fits)
  | trap {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state : type.denote}
      (chosen : test.denote pure.funs (loopEnv env index state) = true)
      (stepRun : ResourceExec host pure program depth (loopModes .owned modes)
        (shift 2 (loopLive test step live)) step (loopEnv env index state)
        world trace (.trapped message) final spent fits) :
      ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index state
        world trace (.trapped message) final
        (pure.loopTestCost depth modes live test step env index state + spent)
        (pure.loopTestFits depth test env index state && fits)

end

private theorem exec_bind_exit {World : Type} {host : Host World}
    {action : Action α} {next : α → Action β} {world trace code final}
    (execution : Exec host action world trace (.exited code) final) :
    Exec host (Action.bind action next) world trace (.exited code) final := by
  simpa only [List.append_nil] using execution.bind (next := next) ⟨rfl, rfl, rfl⟩

private theorem exec_bind_trap {World : Type} {host : Host World}
    {action : Action α} {next : α → Action β} {world trace message final}
    (execution : Exec host action world trace (.trapped message) final) :
    Exec host (Action.bind action next) world trace (.trapped message) final := by
  simpa only [List.append_nil] using execution.bind (next := next) ⟨rfl, rfl, rfl⟩

private def ExecErasure {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool)
    {context : List Ty} {result : ResultTy} (command : Command pureSigs effectSigs context result)
    (env : Env context) (world : World) (trace : List Event) (outcome : Outcome result.denote)
    (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceExec host pure program depth modes live command env world trace outcome final spent fits) :
    Prop :=
  Exec host (command.denote pure.funs (program.funs pure.funs) env) world trace outcome final

private def CallErasure {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    {signature : EffectSig} (callee : EffectVar effectSigs signature) (depth : UInt64)
    (env : Env signature.params) (world : World) (trace : List Event)
    (outcome : Outcome signature.result.denote) (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceCall host pure program callee depth env world trace outcome final spent fits) : Prop :=
  Exec host ((program.funs pure.funs).get callee env) world trace outcome final

private def LoopErasure {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) {context : List Ty} {type : Ty}
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context)
    (remaining index : Nat) (state : type.denote) (world : World) (trace : List Event)
    (outcome : Outcome type.denote) (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceLoopExec host pure program depth modes live test step env
      remaining index state world trace outcome final spent fits) : Prop :=
  LoopExec host remaining index state
    (fun index state => test.denote pure.funs (.cons state (.cons index env)))
    (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
    Action.pure world trace outcome final

private theorem erase_ite_yes {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final} (chosen : condition.denote pure.funs env = true)
    (execution : Exec host (yes.denote pure.funs (program.funs pure.funs) env) world trace outcome final) :
    Exec host ((Command.ite condition yes no).denote pure.funs (program.funs pure.funs) env)
      world trace outcome final := by
  rw [Command.denote, chosen]
  exact execution

private theorem erase_ite_no {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final} (chosen : condition.denote pure.funs env = false)
    (execution : Exec host (no.denote pure.funs (program.funs pure.funs) env) world trace outcome final) :
    Exec host ((Command.ite condition yes no).denote pure.funs (program.funs pure.funs) env)
      world trace outcome final := by
  rw [Command.denote, chosen]
  exact execution

macro "wasi_resource_erasure_steps" : tactic => `(tactic|
  (all_goals intros
   all_goals first
     | assumption
     | exact Exec.pure _ _
     | (apply Exec.bind <;> assumption)
     | (apply exec_bind_exit; assumption)
     | (apply exec_bind_trap; assumption)
     | (apply erase_ite_yes <;> assumption)
     | (apply erase_ite_no <;> assumption)
     | (apply Exec.loop; assumption)
     | exact LoopExec.zero (.pure _ _)
     | (apply LoopExec.stop <;> first | assumption | exact Exec.pure _ _)
     | (apply LoopExec.next <;> assumption)
     | (apply LoopExec.exit <;> assumption)
     | (apply LoopExec.trap <;> assumption)))

theorem ResourceExec.erase {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits}
    (execution : ResourceExec host pure program depth modes live command env
      world trace outcome final spent fits) :
    Exec host (command.denote pure.funs (program.funs pure.funs) env) world trace outcome final := by
  refine ResourceExec.rec (motive_1 := ExecErasure host pure) (motive_2 := CallErasure host pure)
    (motive_3 := LoopErasure host pure)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  wasi_resource_erasure_steps

theorem ResourceCall.erase {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {depth : UInt64} {env : Env signature.params} {world trace outcome final spent fits}
    (execution : ResourceCall host pure program callee depth env world trace outcome final spent fits) :
    Exec host ((program.funs pure.funs).get callee env) world trace outcome final := by
  refine ResourceCall.rec (motive_1 := ExecErasure host pure) (motive_2 := CallErasure host pure)
    (motive_3 := LoopErasure host pure)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  wasi_resource_erasure_steps

theorem ResourceLoopExec.erase {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world trace outcome final spent fits}
    (execution : ResourceLoopExec host pure program depth modes live test step env
      remaining index state world trace outcome final spent fits) :
    LoopExec host remaining index state
      (fun index state => test.denote pure.funs (.cons state (.cons index env)))
      (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
      Action.pure world trace outcome final := by
  refine ResourceLoopExec.rec (motive_1 := ExecErasure host pure) (motive_2 := CallErasure host pure)
    (motive_3 := LoopErasure host pure)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ execution
  wasi_resource_erasure_steps

end Verified.Wasi.Resource
