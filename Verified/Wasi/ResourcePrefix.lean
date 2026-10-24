import Verified.Wasi.ResourceExec
import LeanExe.Wasi.Prefix

namespace Verified.Wasi.Resource

open LeanExe.Wasi

mutual

inductive ResourcePrefix {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    (depth : UInt64) → (modes : List Mode) → (live : Nat → Bool) →
    {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Env context →
    World → List Event → Action result.denote → World → Nat → Bool → Prop where
  | refl (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode) (live : Nat → Bool)
      (command : Command pureSigs effectSigs context result) (env : Env context) (world : World) :
      ResourcePrefix host pure program depth modes live command env world []
        (command.denote pure.funs (program.funs pure.funs) env) world 0 true
  | ret_charge (program : EffectProg pureSigs effectSigs)
      (depth : UInt64) (modes : List Mode) (live : Nat → Bool)
      (value : Expr pureSigs context type) (env : Env context) (world : World) :
      ResourcePrefix host pure program depth modes live (.ret value) env world []
        (.pure (value.denote pure.funs env)) world
        (pure.ownedCost depth modes live value env) (pure.exprFits depth value env)
  | read_charge (program : EffectProg pureSigs effectSigs)
      (depth : UInt64) (modes : List Mode) (live : Nat → Bool)
      (capacity : Expr pureSigs context .word) (env : Env context) (world : World) :
      ResourcePrefix host pure program depth modes live (.read capacity) env world []
        ((Command.read capacity).denote pure.funs (program.funs pure.funs) env) world
        (pure.readCost depth modes live capacity env) (pure.exprFits depth capacity env)
  | exit_charge {program : EffectProg pureSigs effectSigs}
      (code : Expr pureSigs context .word) (env : Env context) (world : World) :
      ResourcePrefix host pure program depth modes live
        (Command.exit code : Command pureSigs effectSigs context result) env world []
        (.exit (code.denote pure.funs env)) world
        (pure.exprCost depth modes live code env) (pure.exprFits depth code env)
  | returned {program : EffectProg pureSigs effectSigs}
      {command : Command pureSigs effectSigs context result} {env : Env context}
      (execution : ResourceExec host pure program depth modes live command env
        world trace (.returned value) final spent fits) :
      ResourcePrefix host pure program depth modes live command env world trace (.pure value) final spent fits
  | bind_left {program : EffectProg pureSigs effectSigs}
      {first : Command pureSigs effectSigs context intermediate}
      {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
      {residual : Action intermediate.denote}
      (progress : ResourcePrefix host pure program depth modes (bindLive intermediate next live)
        first env world trace residual final spent fits) :
      ResourcePrefix host pure program depth modes live (.bind first next) env world trace
        (Action.bind residual fun value =>
          next.denote pure.funs (program.funs pure.funs) (intermediate.bindEnv value env))
        final spent fits
  | bind_right {program : EffectProg pureSigs effectSigs}
      {first : Command pureSigs effectSigs context intermediate}
      {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
      {residual : Action result.denote}
      (firstRun : ResourceExec host pure program depth modes (bindLive intermediate next live)
        first env world firstTrace (.returned value) after firstSpent firstFits)
      (progress : ResourcePrefix host pure program depth (bindModes intermediate modes)
        (shift intermediate.bindCount live) next (intermediate.bindEnv value env)
        after restTrace residual final nextSpent nextFits) :
      ResourcePrefix host pure program depth modes live (.bind first next) env
        world (firstTrace ++ restTrace) residual final (firstSpent + nextSpent) (firstFits && nextFits)
  | ite_charge {program : EffectProg pureSigs effectSigs}
      {condition : Expr pureSigs context .bool}
      {yes no : Command pureSigs effectSigs context result} {env : Env context} (world : World) :
      ResourcePrefix host pure program depth modes live (.ite condition yes no) env world []
        ((Command.ite condition yes no).denote pure.funs (program.funs pure.funs) env) world
        (pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env)
        (pure.exprFits depth condition env)
  | ite_yes {program : EffectProg pureSigs effectSigs}
      {condition : Expr pureSigs context .bool}
      {yes no : Command pureSigs effectSigs context result} {env : Env context}
      {residual : Action result.denote}
      (chosen : condition.denote pure.funs env = true)
      (progress : ResourcePrefix host pure program depth modes live yes env
        world trace residual final spent fits) :
      ResourcePrefix host pure program depth modes live (.ite condition yes no) env
        world trace residual final
        (pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env + spent)
        (pure.exprFits depth condition env && fits)
  | ite_no {program : EffectProg pureSigs effectSigs}
      {condition : Expr pureSigs context .bool}
      {yes no : Command pureSigs effectSigs context result} {env : Env context}
      {residual : Action result.denote}
      (chosen : condition.denote pure.funs env = false)
      (progress : ResourcePrefix host pure program depth modes live no env
        world trace residual final spent fits) :
      ResourcePrefix host pure program depth modes live (.ite condition yes no) env
        world trace residual final
        (pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env + spent)
        (pure.exprFits depth condition env && fits)
  | call {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
      {args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)}
      {env : Env context} {residual : Action signature.result.denote}
      (progress : ResourceCallPrefix host pure program callee (depth + 1)
        (Env.ofFn fun i => (args i).denote pure.funs env) world trace residual final spent fits) :
      ResourcePrefix host pure program depth modes live (.call callee args) env
        world trace residual final
        (pure.argumentCost depth modes live signature args env + spent)
        (pure.argumentFits depth args env && fits)
  | loop_count {program : EffectProg pureSigs effectSigs}
      {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
      {env : Env context} (world : World) :
      ResourcePrefix host pure program depth modes live (.loop count initial test step) env world []
        ((Command.loop count initial test step).denote pure.funs (program.funs pure.funs) env) world
        (pure.loopCountCost depth modes live count initial test step env)
        (pure.exprFits depth count env)
  | loop_init {program : EffectProg pureSigs effectSigs}
      {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
      {env : Env context} (world : World) :
      ResourcePrefix host pure program depth modes live (.loop count initial test step) env world []
        ((Command.loop count initial test step).denote pure.funs (program.funs pure.funs) env) world
        (pure.loopInitCost depth modes live count initial test step env)
        (pure.loopInitFits depth count initial env)
  | loop {program : EffectProg pureSigs effectSigs}
      {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {residual : Action type.denote}
      (progress : ResourceLoopPrefix host pure program depth modes live test step env
        (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env)
        world trace residual final spent fits) :
      ResourcePrefix host pure program depth modes live (.loop count initial test step) env
        world trace residual final
        (pure.loopInitCost depth modes live count initial test step env + spent)
        (pure.loopInitFits depth count initial env && fits)

inductive ResourceCallPrefix {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    {signature : EffectSig} → EffectVar effectSigs signature → UInt64 → Env signature.params →
    World → List Event → Action signature.result.denote → World → Nat → Bool → Prop where
  | guard (program : EffectProg pureSigs effectSigs) (callee : EffectVar effectSigs signature)
      (depth : UInt64) (env : Env signature.params) (world : World) :
      ResourceCallPrefix host pure program callee depth env world []
        ((program.funs pure.funs).get callee env) world 0 (entryFits depth)
  | here {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
      {env : Env function.params}
      {residual : Action function.result.denote}
      (progress : ResourcePrefix host pure rest depth (entryModes function.params function.modes)
        (fun _ => false) function.body env world trace residual final spent fits) :
      ResourceCallPrefix host pure (.cons function rest) .here depth env
        world trace residual final spent (entryFits depth && fits)
  | there {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
      {callee : EffectVar effectSigs signature} {env : Env signature.params}
      {residual : Action signature.result.denote}
      (progress : ResourceCallPrefix host pure rest callee depth env world trace residual final spent fits) :
      ResourceCallPrefix host pure (.cons function rest) (.there callee) depth env
        world trace residual final spent fits

inductive ResourceLoopPrefix {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    UInt64 → List Mode → (Nat → Bool) → {context : List Ty} → {type : Ty} →
    (test : Expr pureSigs (type :: .word :: context) .bool) →
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) → Env context →
    Nat → Nat → type.denote →
    World → List Event → Action type.denote → World → Nat → Bool → Prop where
  | refl {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      (world : World) (remaining index : Nat) (state : type.denote) :
      ResourceLoopPrefix host pure program depth modes live test step env remaining index state
        world [] (loopResume pure program test step env remaining index state) world 0 true
  | test_charge {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      (world : World) (remaining index : Nat) (state : type.denote) :
      ResourceLoopPrefix host pure program depth modes live test step env (remaining + 1) index state
        world [] (loopResume pure program test step env (remaining + 1) index state) world
        (pure.loopTestCost depth modes live test step env index state)
        (pure.loopTestFits depth test env index state)
  | returned {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state value : type.denote}
      (execution : ResourceLoopExec host pure program depth modes live test step env
        remaining index state world trace (.returned value) final spent fits) :
      ResourceLoopPrefix host pure program depth modes live test step env remaining index state
        world trace (.pure value) final spent fits
  | step {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state : type.denote}
      {residual : Action type.denote}
      (chosen : test.denote pure.funs (loopEnv env index state) = true)
      (progress : ResourcePrefix host pure program depth (loopModes .owned modes)
        (shift 2 (loopLive test step live)) step (loopEnv env index state)
        world trace residual final spent fits) :
      ResourceLoopPrefix host pure program depth modes live test step env (remaining + 1) index state
        world trace (Action.bind residual (loopResume pure program test step env remaining (index + 1)))
        final (pure.loopTestCost depth modes live test step env index state + spent)
        (pure.loopTestFits depth test env index state && fits)
  | next {program : EffectProg pureSigs effectSigs}
      {test : Expr pureSigs (type :: .word :: context) .bool}
      {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
      {remaining index : Nat} {state nextState : type.denote}
      {residual : Action type.denote}
      (chosen : test.denote pure.funs (loopEnv env index state) = true)
      (stepRun : ResourceExec host pure program depth (loopModes .owned modes)
        (shift 2 (loopLive test step live)) step (loopEnv env index state)
        world firstTrace (.returned nextState) after stepSpent stepFits)
      (progress : ResourceLoopPrefix host pure program depth modes live test step env
        remaining (index + 1) nextState after restTrace residual final restSpent restFits) :
      ResourceLoopPrefix host pure program depth modes live test step env (remaining + 1) index state
        world (firstTrace ++ restTrace) residual final
        (pure.loopTestCost depth modes live test step env index state + stepSpent + restSpent)
        (pure.loopTestFits depth test env index state && stepFits && restFits)

end

private def PrefixErasure {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) {context : List Ty} {result : ResultTy}
    (command : Command pureSigs effectSigs context result) (env : Env context)
    (world : World) (trace : List Event) (residual : Action result.denote) (final : World)
    (spent : Nat) (fits : Bool)
    (_ : ResourcePrefix host pure program depth modes live command env world trace residual final spent fits) :
    Prop :=
  Prefix host (command.denote pure.funs (program.funs pure.funs) env) world trace residual final

private def CallPrefixErasure {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    {signature : EffectSig} (callee : EffectVar effectSigs signature) (depth : UInt64)
    (env : Env signature.params) (world : World) (trace : List Event)
    (residual : Action signature.result.denote) (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceCallPrefix host pure program callee depth env world trace residual final spent fits) : Prop :=
  Prefix host ((program.funs pure.funs).get callee env) world trace residual final

private def LoopPrefixErasure {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) {context : List Ty} {type : Ty}
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context)
    (remaining index : Nat) (state : type.denote) (world : World) (trace : List Event)
    (residual : Action type.denote) (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceLoopPrefix host pure program depth modes live test step env
      remaining index state world trace residual final spent fits) : Prop :=
  Prefix host (loopResume pure program test step env remaining index state) world trace residual final

private theorem prefix_ite_yes {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final} (chosen : condition.denote pure.funs env = true)
    (progress : Prefix host (yes.denote pure.funs (program.funs pure.funs) env) world trace residual final) :
    Prefix host ((Command.ite condition yes no).denote pure.funs (program.funs pure.funs) env)
      world trace residual final := by
  rw [Command.denote, chosen]
  exact progress

private theorem prefix_ite_no {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final} (chosen : condition.denote pure.funs env = false)
    (progress : Prefix host (no.denote pure.funs (program.funs pure.funs) env) world trace residual final) :
    Prefix host ((Command.ite condition yes no).denote pure.funs (program.funs pure.funs) env)
      world trace residual final := by
  rw [Command.denote, chosen]
  exact progress

private theorem prefix_loop_returned {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world trace value final spent fits}
    (execution : ResourceLoopExec host pure program depth modes live test step env
      remaining index state world trace (.returned value) final spent fits) :
    Prefix host (loopResume pure program test step env remaining index state)
      world trace (.pure value) final :=
  Exec.returned_prefix _ execution.erase.resume

private theorem prefix_loop_step {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world trace residual final}
    (chosen : test.denote pure.funs (loopEnv env index state) = true)
    (progress : Prefix host (step.denote pure.funs (program.funs pure.funs) (loopEnv env index state))
      world trace residual final) :
    Prefix host (loopResume pure program test step env (remaining + 1) index state) world trace
      (Action.bind residual (loopResume pure program test step env remaining (index + 1))) final := by
  change Prefix host (if test.denote pure.funs (loopEnv env index state) then _ else _)
    world trace _ final
  rw [chosen]
  exact progress.bind

private theorem prefix_loop_next {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world firstTrace nextState after restTrace residual final}
    (chosen : test.denote pure.funs (loopEnv env index state) = true)
    (execution : Exec host (step.denote pure.funs (program.funs pure.funs) (loopEnv env index state))
      world firstTrace (.returned nextState) after)
    (progress : Prefix host (loopResume pure program test step env remaining (index + 1) nextState)
      after restTrace residual final) :
    Prefix host (loopResume pure program test step env (remaining + 1) index state)
      world (firstTrace ++ restTrace) residual final := by
  change Prefix host (if test.denote pure.funs (loopEnv env index state) then _ else _)
    world (firstTrace ++ restTrace) residual final
  rw [chosen]
  exact Prefix.bind_after execution progress

macro "wasi_resource_prefix_erasure_steps" : tactic => `(tactic|
  (all_goals intros
   all_goals first
     | assumption
     | exact Prefix.refl _ _
     | (apply Exec.returned_prefix; apply ResourceExec.erase; assumption)
     | (apply Prefix.bind; assumption)
     | (apply Prefix.bind_after <;> first | assumption | (apply ResourceExec.erase; assumption))
     | (apply prefix_ite_yes <;> assumption)
     | (apply prefix_ite_no <;> assumption)
     | (apply Prefix.trans Prefix.loop; assumption)
     | (apply prefix_loop_returned; assumption)
     | (apply prefix_loop_step <;> assumption)
     | (apply prefix_loop_next <;> first | assumption | (apply ResourceExec.erase; assumption))))

theorem ResourcePrefix.erase {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final spent fits}
    (progress : ResourcePrefix host pure program depth modes live command env
      world trace residual final spent fits) :
    Prefix host (command.denote pure.funs (program.funs pure.funs) env) world trace residual final := by
  refine ResourcePrefix.rec (motive_1 := PrefixErasure host pure)
    (motive_2 := CallPrefixErasure host pure) (motive_3 := LoopPrefixErasure host pure)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ progress
  wasi_resource_prefix_erasure_steps

theorem ResourceCallPrefix.erase {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {callee : EffectVar effectSigs signature}
    {depth : UInt64} {env : Env signature.params} {world trace residual final spent fits}
    (progress : ResourceCallPrefix host pure program callee depth env world trace residual final spent fits) :
    Prefix host ((program.funs pure.funs).get callee env) world trace residual final := by
  refine ResourceCallPrefix.rec (motive_1 := PrefixErasure host pure)
    (motive_2 := CallPrefixErasure host pure) (motive_3 := LoopPrefixErasure host pure)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ progress
  wasi_resource_prefix_erasure_steps

theorem ResourceLoopPrefix.erase {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world trace residual final spent fits}
    (progress : ResourceLoopPrefix host pure program depth modes live test step env
      remaining index state world trace residual final spent fits) :
    Prefix host (loopResume pure program test step env remaining index state)
      world trace residual final := by
  refine ResourceLoopPrefix.rec (motive_1 := PrefixErasure host pure)
    (motive_2 := CallPrefixErasure host pure) (motive_3 := LoopPrefixErasure host pure)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ progress
  wasi_resource_prefix_erasure_steps

def PrefixBound {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode) (live : Nat → Bool)
    (command : Command pureSigs effectSigs context result) (env : Env context)
    (world : World) (budget : Nat) : Prop :=
  ∀ trace residual final spent fits,
    ResourcePrefix host pure program depth modes live command env world trace residual final spent fits →
      spent ≤ budget ∧ fits = true

def CallPrefixBound {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (callee : EffectVar effectSigs signature)
    (depth : UInt64) (env : Env signature.params) (world : World) (budget : Nat) : Prop :=
  ∀ trace residual final spent fits,
    ResourceCallPrefix host pure program callee depth env world trace residual final spent fits →
      spent ≤ budget ∧ fits = true

def LoopPrefixBound {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode) (live : Nat → Bool)
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) (remaining index : Nat) (state : type.denote)
    (world : World) (budget : Nat) : Prop :=
  ∀ trace residual final spent fits,
    ResourceLoopPrefix host pure program depth modes live test step env remaining index state
      world trace residual final spent fits → spent ≤ budget ∧ fits = true

theorem PrefixBound.ret {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {value : Expr pureSigs context type} {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.ret value) env world budget) :
    pure.ownedCost depth modes live value env ≤ budget ∧ pure.exprFits depth value env = true :=
  bounded _ _ _ _ _ (.ret_charge program depth modes live value env world)

theorem PrefixBound.read {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {capacity : Expr pureSigs context .word} {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.read capacity) env world budget) :
    pure.readCost depth modes live capacity env ≤ budget ∧ pure.exprFits depth capacity env = true :=
  bounded _ _ _ _ _ (.read_charge program depth modes live capacity env world)

end Verified.Wasi.Resource
