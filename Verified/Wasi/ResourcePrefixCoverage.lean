import Verified.Wasi.ResourceAdvanceCoverage

namespace Verified.Wasi.Resource

open LeanExe.Wasi

theorem ResourcePrefix.completed {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final spent fits value}
    (progress : ResourcePrefix host pure program depth modes live command env world trace residual final spent fits)
    (pureEq : residual = .pure value) :
    ∃ nextSpent nextFits, ResourceExec host pure program depth modes live command env
      world trace (.returned value) final nextSpent nextFits := by
  have erased := progress.erase
  rw [pureEq] at erased
  exact ResourceExec.ofExec command depth modes live env (prefix_pure_exec erased)

private theorem bind_continue_advance {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {first : Command pureSigs effectSigs context intermediate}
    {next : Command pureSigs effectSigs (intermediate.extend context) result} {env : Env context}
    {world firstTrace value after firstSpent firstFits nextTrace residual final}
    (execution : ResourceExec host pure program depth modes (bindLive intermediate next live)
      first env world firstTrace (.returned value) after firstSpent firstFits)
    (advance : PrefixAdvance host
      (next.denote pure.funs (program.funs pure.funs) (intermediate.bindEnv value env))
      after nextTrace residual final) :
    ∃ spent fits, ResourcePrefix host pure program depth modes live (.bind first next) env
      world (firstTrace ++ nextTrace) residual final spent fits := by
  obtain ⟨_, _, progress⟩ := ResourcePrefix.ofAdvance next depth (bindModes intermediate modes)
    (shift intermediate.bindCount live) (intermediate.bindEnv value env) advance
  exact ⟨_, _, .bind_right execution progress⟩

private theorem loop_continue_advance {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world firstTrace nextState after firstSpent firstFits nextTrace residual final}
    (chosen : test.denote pure.funs (loopEnv env index state) = true)
    (execution : ResourceExec host pure program depth (loopModes .owned modes)
      (shift 2 (loopLive test step live)) step (loopEnv env index state)
      world firstTrace (.returned nextState) after firstSpent firstFits)
    (advance : PrefixAdvance host (loopResume pure program test step env remaining (index + 1) nextState)
      after nextTrace residual final) :
    ∃ spent fits, ResourceLoopPrefix host pure program depth modes live test step env
      (remaining + 1) index state world (firstTrace ++ nextTrace) residual final spent fits := by
  obtain ⟨_, _, progress⟩ := ResourceLoopPrefix.ofAdvance remaining advance
  exact ⟨_, _, .next chosen execution progress⟩

private def PrefixAdvanceClosed {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) {context : List Ty} {result : ResultTy}
    (command : Command pureSigs effectSigs context result) (env : Env context)
    (world : World) (trace : List Event) (residual : Action result.denote) (final : World)
    (spent : Nat) (fits : Bool)
    (_ : ResourcePrefix host pure program depth modes live command env world trace residual final spent fits) :
    Prop :=
  ∀ {nextTrace nextResidual nextFinal}, PrefixAdvance host residual final nextTrace nextResidual nextFinal →
    ∃ nextSpent nextFits, ResourcePrefix host pure program depth modes live command env
      world (trace ++ nextTrace) nextResidual nextFinal nextSpent nextFits

private def CallAdvanceClosed {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    {signature : EffectSig} (callee : EffectVar effectSigs signature) (depth : UInt64)
    (env : Env signature.params) (world : World) (trace : List Event)
    (residual : Action signature.result.denote) (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceCallPrefix host pure program callee depth env world trace residual final spent fits) : Prop :=
  ∀ {nextTrace nextResidual nextFinal}, PrefixAdvance host residual final nextTrace nextResidual nextFinal →
    ∃ nextSpent nextFits, ResourceCallPrefix host pure program callee depth env
      world (trace ++ nextTrace) nextResidual nextFinal nextSpent nextFits

private def LoopAdvanceClosed {World : Type} (host : Host World) (pure : PureContext pureSigs)
    {effectSigs : List EffectSig} (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) {context : List Ty} {type : Ty}
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context)
    (remaining index : Nat) (state : type.denote) (world : World) (trace : List Event)
    (residual : Action type.denote) (final : World) (spent : Nat) (fits : Bool)
    (_ : ResourceLoopPrefix host pure program depth modes live test step env
      remaining index state world trace residual final spent fits) : Prop :=
  ∀ {nextTrace nextResidual nextFinal}, PrefixAdvance host residual final nextTrace nextResidual nextFinal →
    ∃ nextSpent nextFits, ResourceLoopPrefix host pure program depth modes live test step env
      remaining index state world (trace ++ nextTrace) nextResidual nextFinal nextSpent nextFits

theorem ResourcePrefix.advance {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final spent fits}
    (progress : ResourcePrefix host pure program depth modes live command env
      world trace residual final spent fits) :
    ∀ {nextTrace nextResidual nextFinal}, PrefixAdvance host residual final nextTrace nextResidual nextFinal →
      ∃ nextSpent nextFits, ResourcePrefix host pure program depth modes live command env
        world (trace ++ nextTrace) nextResidual nextFinal nextSpent nextFits := by
  refine ResourcePrefix.rec (motive_1 := PrefixAdvanceClosed host pure)
    (motive_2 := CallAdvanceClosed host pure) (motive_3 := LoopAdvanceClosed host pure)
    ?commandRefl ?retCharge ?readCharge ?exitCharge ?commandReturned ?bindLeft ?bindRight
    ?iteCharge ?iteYes ?iteNo ?call ?loopCount ?loopInit ?loopBody ?callGuard ?callHere ?callThere
    ?loopRefl ?testCharge ?loopReturned ?loopStep ?loopNext progress
  all_goals intros
  all_goals simp only [PrefixAdvanceClosed, CallAdvanceClosed, LoopAdvanceClosed] at *
  all_goals intros
  case commandRefl =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourcePrefix.ofAdvance _ _ _ _ _ advance
  case retCharge => rename_i advance; cases advance
  case readCharge =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourcePrefix.ofAdvance _ _ _ _ _ advance
  case exitCharge => rename_i advance; cases advance
  case commandReturned => rename_i advance; cases advance
  case bindLeft =>
    rename_i firstProgress firstIH nextTrace nextResidual nextFinal advance
    rcases advance_bind_cases advance with ⟨middle, firstAdvance, rfl⟩ | ⟨value, pureEq, nextAdvance⟩
    · obtain ⟨_, _, progress⟩ := firstIH firstAdvance
      exact ⟨_, _, .bind_left progress⟩
    · obtain ⟨_, _, execution⟩ := firstProgress.completed pureEq
      exact bind_continue_advance execution nextAdvance
  case bindRight =>
    rename_i execution nextProgress nextIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := nextIH advance
    rw [List.append_assoc]
    exact ⟨_, _, .bind_right execution progress⟩
  case iteCharge =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourcePrefix.ofAdvance _ _ _ _ _ advance
  case iteYes =>
    rename_i chosen branchProgress branchIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := branchIH advance
    exact ⟨_, _, .ite_yes chosen progress⟩
  case iteNo =>
    rename_i chosen branchProgress branchIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := branchIH advance
    exact ⟨_, _, .ite_no chosen progress⟩
  case call =>
    rename_i callProgress callIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := callIH advance
    exact ⟨_, _, .call progress⟩
  case loopCount =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourcePrefix.ofAdvance _ _ _ _ _ advance
  case loopInit =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourcePrefix.ofAdvance _ _ _ _ _ advance
  case loopBody =>
    rename_i loopProgress loopIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := loopIH advance
    exact ⟨_, _, .loop progress⟩
  case callGuard =>
    rename_i nextTrace nextResidual nextFinal advance
    exact program_calls_advance_covered host pure _ _ _ _ _ _ _ _ advance
  case callHere =>
    rename_i bodyProgress bodyIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := bodyIH advance
    exact ⟨_, _, .here progress⟩
  case callThere =>
    rename_i callProgress callIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := callIH advance
    exact ⟨_, _, .there progress⟩
  case loopRefl =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourceLoopPrefix.ofAdvance _ advance
  case testCharge =>
    rename_i nextTrace nextResidual nextFinal advance
    exact ResourceLoopPrefix.ofAdvance _ advance
  case loopReturned => rename_i advance; cases advance
  case loopStep =>
    rename_i chosen stepProgress stepIH nextTrace nextResidual nextFinal advance
    rcases advance_bind_cases advance with ⟨middle, stepAdvance, rfl⟩ | ⟨value, pureEq, restAdvance⟩
    · obtain ⟨_, _, progress⟩ := stepIH stepAdvance
      exact ⟨_, _, .step chosen progress⟩
    · obtain ⟨_, _, execution⟩ := stepProgress.completed pureEq
      exact loop_continue_advance chosen execution restAdvance
  case loopNext =>
    rename_i chosen execution loopProgress loopIH nextTrace nextResidual nextFinal advance
    obtain ⟨_, _, progress⟩ := loopIH advance
    rw [List.append_assoc]
    exact ⟨_, _, .next chosen execution progress⟩

private theorem ResourcePrefix.extendProgress {World : Type} {host : Host World}
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {residual : Action result.denote} {after trace nextResidual final}
    (rest : PrefixProgress host residual after trace nextResidual final) :
    ∀ {world first spent fits}, ResourcePrefix host pure program depth modes live command env
      world first residual after spent fits →
      ∃ nextSpent nextFits, ResourcePrefix host pure program depth modes live command env
        world (first ++ trace) nextResidual final nextSpent nextFits := by
  induction rest with
  | refl =>
    intro world first spent fits progress
    exact ⟨_, _, by simpa only [List.append_nil] using progress⟩
  | advance advance =>
    intro world first spent fits progress
    exact progress.advance advance
  | trans head tail headIH tailIH =>
    intro world first spent fits progress
    obtain ⟨_, _, progress⟩ := headIH progress
    obtain ⟨_, _, progress⟩ := tailIH progress
    exact ⟨_, _, by simpa only [List.append_assoc] using progress⟩

theorem ResourcePrefix.ofPrefix {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} (command : Command pureSigs effectSigs context result)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) (env : Env context)
    {world trace residual final}
    (progress : Prefix host (command.denote pure.funs (program.funs pure.funs) env)
      world trace residual final) :
    ∃ spent fits, ResourcePrefix host pure program depth modes live command env
      world trace residual final spent fits := by
  exact ResourcePrefix.extendProgress progress.progress (.refl program depth modes live command env world)

end Verified.Wasi.Resource
