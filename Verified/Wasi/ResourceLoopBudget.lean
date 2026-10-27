import Verified.Wasi.ResourceBudget

namespace Verified.Wasi.Resource

open LeanExe.Wasi

theorem PrefixBound.loop_count {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.loop count initial test step) env world budget) :
    pure.loopCountCost depth modes live count initial test step env ≤ budget ∧
      pure.exprFits depth count env = true :=
  bounded _ _ _ _ _ (.loop_count world)

theorem PrefixBound.loop_init {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.loop count initial test step) env world budget) :
    pure.loopInitCost depth modes live count initial test step env ≤ budget ∧
      pure.loopInitFits depth count initial env = true :=
  bounded _ _ _ _ _ (.loop_init world)

theorem PrefixBound.loop_body {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.loop count initial test step) env world budget) :
    LoopPrefixBound host pure program depth modes live test step env
      (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env) world
      (budget - pure.loopInitCost depth modes live count initial test step env) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.loop progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

theorem LoopPrefixBound.returned {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world trace value final spent fits budget}
    (bounded : LoopPrefixBound host pure program depth modes live test step env
      remaining index state world budget)
    (execution : ResourceLoopExec host pure program depth modes live test step env
      remaining index state world trace (.returned value) final spent fits) :
    spent ≤ budget ∧ fits = true :=
  bounded _ _ _ _ _ (.returned execution)

theorem LoopPrefixBound.test {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world budget}
    (bounded : LoopPrefixBound host pure program depth modes live test step env
      (remaining + 1) index state world budget) :
    pure.loopTestCost depth modes live test step env index state ≤ budget ∧
      pure.loopTestFits depth test env index state = true :=
  bounded _ _ _ _ _ (.test_charge world remaining index state)

theorem LoopPrefixBound.step {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state world budget}
    (bounded : LoopPrefixBound host pure program depth modes live test step env
      (remaining + 1) index state world budget)
    (chosen : test.denote pure.funs (loopEnv env index state) = true) :
    PrefixBound host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
      step (loopEnv env index state) world
      (budget - pure.loopTestCost depth modes live test step env index state) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.step chosen progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

theorem LoopPrefixBound.next {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
    {remaining index state nextState world firstTrace after stepSpent stepFits budget}
    (bounded : LoopPrefixBound host pure program depth modes live test step env
      (remaining + 1) index state world budget)
    (chosen : test.denote pure.funs (loopEnv env index state) = true)
    (stepRun : ResourceExec host pure program depth (loopModes .owned modes)
      (shift 2 (loopLive test step live)) step (loopEnv env index state)
      world firstTrace (.returned nextState) after stepSpent stepFits) :
    LoopPrefixBound host pure program depth modes live test step env remaining (index + 1) nextState after
      (budget - pure.loopTestCost depth modes live test step env index state - stepSpent) := by
  intro trace residual final spent fits progress
  obtain ⟨total, fit⟩ := bounded _ _ _ _ _ (.next chosen stepRun progress)
  simp only [Bool.and_eq_true] at fit
  exact ⟨by omega, fit.2⟩

end Verified.Wasi.Resource
