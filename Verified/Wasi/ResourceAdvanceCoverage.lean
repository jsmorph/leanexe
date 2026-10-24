import Verified.Wasi.ResourceCoverage
import Verified.Wasi.ResourcePrefix
import Verified.Wasi.ResourceNativePrefix

namespace Verified.Wasi.Resource

open LeanExe.Wasi

def CallsAdvanceCovered {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) : Prop :=
  ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature) (depth : UInt64)
    (env : Env signature.params) world trace residual after,
    PrefixAdvance host ((program.funs pure.funs).get callee env) world trace residual after →
      ∃ spent fits, ResourceCallPrefix host pure program callee depth env
        world trace residual after spent fits

theorem command_advance_coverage {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} (calls : CallsAdvanceCovered host pure program)
    (command : Command pureSigs effectSigs context result) :
    ∀ (depth : UInt64) (modes : List Mode) (live : Nat → Bool) (env : Env context)
      world trace residual after,
    PrefixAdvance host (command.denote pure.funs (program.funs pure.funs) env) world trace residual after →
      ∃ spent fits, ResourcePrefix host pure program depth modes live command env
        world trace residual after spent fits := by
  induction command with
  | unit => intro depth modes live env world trace residual after advance; cases advance
  | ret value => intro depth modes live env world trace residual after advance; cases advance
  | read capacity =>
    intro depth modes live env world trace residual after advance
    cases advance with
    | read_reject bound =>
      exact ⟨_, _, .returned (.read program depth modes live capacity env
        (.read_reject bound (.pure _ _)))⟩
    | read_return bound reply =>
      exact ⟨_, _, .returned (.read program depth modes live capacity env
        (.read_return bound reply (.pure _ _)))⟩
  | write output bytes =>
    intro depth modes live env world trace residual after advance
    cases output <;> cases advance with
    | write_return reply => exact ⟨_, _, .returned (.write (.write_return reply (.pure _ _)))⟩
  | exit code => intro depth modes live env world trace residual after advance; cases advance
  | @bind context intermediate result first next firstCovered nextCovered =>
    intro depth modes live env world trace residual after advance
    rcases advance_bind_cases
      (action := first.denote pure.funs (program.funs pure.funs) env)
      (next := fun value => next.denote pure.funs (program.funs pure.funs)
        (intermediate.bindEnv value env)) advance with
      ⟨middle, firstAdvance, rfl⟩ | ⟨value, pureEq, nextAdvance⟩
    · obtain ⟨_, _, progress⟩ := firstCovered depth modes (bindLive intermediate next live)
        env _ _ _ _ firstAdvance
      exact ⟨_, _, .bind_left progress⟩
    · obtain ⟨_, _, execution⟩ := ResourceExec.ofExec first depth modes
        (bindLive intermediate next live) env (exec_of_pure world pureEq)
      obtain ⟨_, _, progress⟩ := nextCovered depth (bindModes intermediate modes)
        (shift intermediate.bindCount live) (intermediate.bindEnv value env) _ _ _ _ nextAdvance
      exact ⟨_, _, .bind_right execution progress⟩
  | ite condition yes no yesCovered noCovered =>
    intro depth modes live env world trace residual after advance
    cases chosen : condition.denote pure.funs env with
    | false =>
      obtain ⟨_, _, progress⟩ := noCovered depth modes live env _ _ _ _
        (by simpa only [Command.denote, chosen, Bool.cond_false] using advance)
      exact ⟨_, _, .ite_no chosen progress⟩
    | true =>
      obtain ⟨_, _, progress⟩ := yesCovered depth modes live env _ _ _ _
        (by simpa only [Command.denote, chosen, Bool.cond_true] using advance)
      exact ⟨_, _, .ite_yes chosen progress⟩
  | call callee args =>
    intro depth modes live env world trace residual after advance
    obtain ⟨_, _, progress⟩ := calls callee (depth + 1)
      (Env.ofFn fun i => (args i).denote pure.funs env) _ _ _ _ advance
    exact ⟨_, _, .call progress⟩
  | loop count initial test step stepCovered =>
    intro depth modes live env world trace residual after advance
    cases advance
    exact ⟨_, _, .loop (.refl world _ _ _)⟩

theorem program_calls_advance_covered {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) : CallsAdvanceCovered host pure program := by
  induction program with
  | nil => intro signature callee; exact nomatch callee
  | cons function rest restCovered =>
    intro signature callee depth env world trace residual after advance
    cases callee with
    | here =>
      obtain ⟨_, _, progress⟩ := command_advance_coverage restCovered function.body depth
        (entryModes function.params function.modes) (fun _ => false) env _ _ _ _ advance
      exact ⟨_, _, .here progress⟩
    | there callee =>
      obtain ⟨_, _, progress⟩ := restCovered callee depth env _ _ _ _ advance
      exact ⟨_, _, .there progress⟩

theorem ResourcePrefix.ofAdvance {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} (command : Command pureSigs effectSigs context result)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) (env : Env context)
    {world trace residual after}
    (advance : PrefixAdvance host (command.denote pure.funs (program.funs pure.funs) env)
      world trace residual after) :
    ∃ spent fits, ResourcePrefix host pure program depth modes live command env
      world trace residual after spent fits :=
  command_advance_coverage (program_calls_advance_covered host pure program) command
    depth modes live env _ _ _ _ advance

theorem ResourceLoopPrefix.ofAdvance {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    (remaining : Nat) : ∀ {index state world trace residual after},
    PrefixAdvance host (loopResume pure program test step env remaining index state)
      world trace residual after →
      ∃ spent fits, ResourceLoopPrefix host pure program depth modes live test step env
        remaining index state world trace residual after spent fits := by
  induction remaining with
  | zero => intro index state world trace residual after advance; cases advance
  | succ remaining ih =>
    intro index state world trace residual after advance
    cases chosen : test.denote pure.funs (loopEnv env index state) with
    | false =>
      change PrefixAdvance host (if test.denote pure.funs (loopEnv env index state) then _ else _)
        world trace residual after at advance
      rw [chosen] at advance
      cases advance
    | true =>
      change PrefixAdvance host (if test.denote pure.funs (loopEnv env index state) then _ else _)
        world trace residual after at advance
      rw [chosen] at advance
      rcases advance_bind_cases
        (action := step.denote pure.funs (program.funs pure.funs) (loopEnv env index state))
        (next := loopResume pure program test step env remaining (index + 1)) advance with
        ⟨middle, stepAdvance, rfl⟩ | ⟨value, pureEq, restAdvance⟩
      · obtain ⟨_, _, progress⟩ := ResourcePrefix.ofAdvance step depth (loopModes .owned modes)
          (shift 2 (loopLive test step live)) (loopEnv env index state) stepAdvance
        exact ⟨_, _, .step chosen progress⟩
      · obtain ⟨_, _, execution⟩ := ResourceExec.ofExec step depth (loopModes .owned modes)
          (shift 2 (loopLive test step live)) (loopEnv env index state) (exec_of_pure world pureEq)
        obtain ⟨_, _, progress⟩ := ih restAdvance
        exact ⟨_, _, .next chosen execution progress⟩

end Verified.Wasi.Resource
