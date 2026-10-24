import Verified.Wasi.ResourceExec

namespace Verified.Wasi.Resource

open LeanExe.Wasi

def CallsCovered {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) : Prop :=
  ∀ {signature : EffectSig} (callee : EffectVar effectSigs signature) (depth : UInt64)
    (env : Env signature.params) world trace outcome final,
    Exec host ((program.funs pure.funs).get callee env) world trace outcome final →
      ∃ spent fits, ResourceCall host pure program callee depth env world trace outcome final spent fits

private theorem loop_coverage {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    (stepCovered : ∀ (stepModes : List Mode) (stepLive : Nat → Bool)
      (stepEnv : Env (type :: .word :: context)) world trace outcome final,
      Exec host (step.denote pure.funs (program.funs pure.funs) stepEnv) world trace outcome final →
        ∃ spent fits, ResourceExec host pure program depth stepModes stepLive step stepEnv
          world trace outcome final spent fits)
    (remaining : Nat) : ∀ index state world trace outcome final,
    LoopExec host remaining index state
      (fun index state => test.denote pure.funs (.cons state (.cons index env)))
      (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
      Action.pure world trace outcome final →
        ∃ spent fits, ResourceLoopExec host pure program depth modes live test step env
          remaining index state world trace outcome final spent fits := by
  induction remaining with
  | zero =>
    intro index state world trace outcome final execution
    cases execution with
    | zero execution =>
      cases execution
      exact ⟨_, _, .zero world index state⟩
  | succ remaining ih =>
    intro index state world trace outcome final execution
    cases execution with
    | stop chosen execution =>
      cases execution
      exact ⟨_, _, .stop world chosen⟩
    | next chosen stepRun restRun =>
      obtain ⟨_, _, stepRun⟩ := stepCovered (loopModes .owned modes) (shift 2 (loopLive test step live))
        (loopEnv env index state) _ _ _ _ stepRun
      obtain ⟨_, _, restRun⟩ := ih _ _ _ _ _ _ restRun
      exact ⟨_, _, .next chosen stepRun restRun⟩
    | exit chosen stepRun =>
      obtain ⟨_, _, stepRun⟩ := stepCovered (loopModes .owned modes) (shift 2 (loopLive test step live))
        (loopEnv env index state) _ _ _ _ stepRun
      exact ⟨_, _, .exit chosen stepRun⟩
    | trap chosen stepRun =>
      obtain ⟨_, _, stepRun⟩ := stepCovered (loopModes .owned modes) (shift 2 (loopLive test step live))
        (loopEnv env index state) _ _ _ _ stepRun
      exact ⟨_, _, .trap chosen stepRun⟩

theorem command_coverage {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} (calls : CallsCovered host pure program)
    (command : Command pureSigs effectSigs context result) :
    ∀ (depth : UInt64) (modes : List Mode) (live : Nat → Bool) (env : Env context)
      world trace outcome final,
    Exec host (command.denote pure.funs (program.funs pure.funs) env) world trace outcome final →
      ∃ spent fits, ResourceExec host pure program depth modes live command env
        world trace outcome final spent fits := by
  induction command with
  | unit =>
    intro depth modes live env world trace outcome final execution
    cases execution
    exact ⟨_, _, .unit program depth modes live env world⟩
  | ret value =>
    intro depth modes live env world trace outcome final execution
    cases execution
    exact ⟨_, _, .ret program depth modes live value env world⟩
  | read capacity =>
    intro depth modes live env world trace outcome final execution
    exact ⟨_, _, .read program depth modes live capacity env execution⟩
  | write output bytes =>
    intro depth modes live env world trace outcome final execution
    exact ⟨_, _, .write execution⟩
  | exit code =>
    intro depth modes live env world trace outcome final execution
    exact ⟨_, _, .exit execution⟩
  | @bind context intermediate result first next firstCovered nextCovered =>
    intro depth modes live env world trace outcome final execution
    obtain ⟨after, firstTrace, middle, restTrace, firstRun, nextRun, rfl⟩ := Exec.bind_iff.mp execution
    obtain ⟨_, _, firstRun⟩ := firstCovered depth modes (bindLive intermediate next live)
      env _ _ _ _ firstRun
    cases middle with
    | returned value =>
      obtain ⟨_, _, nextRun⟩ := nextCovered depth (bindModes intermediate modes)
        (shift intermediate.bindCount live) (intermediate.bindEnv value env) _ _ _ _ nextRun
      exact ⟨_, _, .bind_return firstRun nextRun⟩
    | exited code =>
      obtain ⟨rfl, rfl, rfl⟩ := nextRun
      simp only [List.append_nil]
      exact ⟨_, _, .bind_exit firstRun⟩
    | trapped message =>
      obtain ⟨rfl, rfl, rfl⟩ := nextRun
      simp only [List.append_nil]
      exact ⟨_, _, .bind_trap firstRun⟩
  | ite condition yes no yesCovered noCovered =>
    intro depth modes live env world trace outcome final execution
    cases chosen : condition.denote pure.funs env with
    | false =>
      obtain ⟨_, _, execution⟩ := noCovered depth modes live env _ _ _ _
        (by simpa only [Command.denote, chosen, Bool.cond_false] using execution)
      exact ⟨_, _, .ite_no chosen execution⟩
    | true =>
      obtain ⟨_, _, execution⟩ := yesCovered depth modes live env _ _ _ _
        (by simpa only [Command.denote, chosen, Bool.cond_true] using execution)
      exact ⟨_, _, .ite_yes chosen execution⟩
  | call callee args =>
    intro depth modes live env world trace outcome final execution
    obtain ⟨_, _, execution⟩ := calls callee (depth + 1)
      (Env.ofFn fun i => (args i).denote pure.funs env) _ _ _ _ execution
    exact ⟨_, _, .call execution⟩
  | loop count initial test step stepCovered =>
    intro depth modes live env world trace outcome final execution
    cases execution with
    | loop execution =>
      obtain ⟨_, _, execution⟩ := loop_coverage (stepCovered depth) _ _ _ _ _ _ _ execution
      exact ⟨_, _, .loop execution⟩

theorem program_calls_covered {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) : CallsCovered host pure program := by
  induction program with
  | nil => intro signature callee; exact nomatch callee
  | cons function rest restCovered =>
    intro signature callee depth env world trace outcome final execution
    cases callee with
    | here =>
      obtain ⟨_, _, execution⟩ := command_coverage restCovered function.body depth
        (entryModes function.params function.modes) (fun _ => false) env _ _ _ _ execution
      exact ⟨_, _, .here execution⟩
    | there callee =>
      obtain ⟨_, _, execution⟩ := restCovered callee depth env _ _ _ _ execution
      exact ⟨_, _, .there execution⟩

theorem ResourceExec.ofExec {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} (command : Command pureSigs effectSigs context result)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) (env : Env context)
    {world trace outcome final}
    (execution : Exec host (command.denote pure.funs (program.funs pure.funs) env) world trace outcome final) :
    ∃ spent fits, ResourceExec host pure program depth modes live command env
      world trace outcome final spent fits :=
  command_coverage (program_calls_covered host pure program) command depth modes live env _ _ _ _ execution

end Verified.Wasi.Resource
