import Verified.Wasi.ResourceLoopBudget

namespace Verified.Wasi.Resource

open LeanExe.Wasi

inductive ResourceLoopHead {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) {context : List Ty} {type : Ty}
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context)
    (initialRemaining initialIndex : Nat) (initialState : type.denote) (initialWorld : World) :
    Nat → Nat → type.denote → World → List Event → Nat → Bool → Prop where
  | refl : ResourceLoopHead host pure program depth modes live test step env
      initialRemaining initialIndex initialState initialWorld
      initialRemaining initialIndex initialState initialWorld [] 0 true
  | next {remaining index : Nat} {state nextState : type.denote}
      {world after : World} {trace first : List Event} {spent stepSpent : Nat} {fits stepFits : Bool}
      (history : ResourceLoopHead host pure program depth modes live test step env
        initialRemaining initialIndex initialState initialWorld (remaining + 1) index state world trace spent fits)
      (chosen : test.denote pure.funs (loopEnv env index state) = true)
      (execution : ResourceExec host pure program depth (loopModes .owned modes)
        (shift 2 (loopLive test step live)) step (loopEnv env index state)
        world first (.returned nextState) after stepSpent stepFits) :
      ResourceLoopHead host pure program depth modes live test step env
        initialRemaining initialIndex initialState initialWorld remaining (index + 1) nextState after
        (trace ++ first) (spent + pure.loopTestCost depth modes live test step env index state + stepSpent)
        (fits && pure.loopTestFits depth test env index state && stepFits)

namespace ResourceLoopHead

variable {World : Type} {host : Host World} {pure : PureContext pureSigs}
  {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
  {context : List Ty} {type : Ty} {test : Expr pureSigs (type :: .word :: context) .bool}
  {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)} {env : Env context}
  {initialRemaining initialIndex remaining index : Nat} {initialState state : type.denote}
  {initialWorld world : World} {trace : List Event} {spent : Nat} {fits : Bool}

theorem remaining_index (history : ResourceLoopHead host pure program depth modes live test step env
    initialRemaining initialIndex initialState initialWorld remaining index state world trace spent fits) :
    remaining + index = initialRemaining + initialIndex := by
  induction history with
  | refl => rfl
  | next _ _ _ ih => omega

theorem complete (history : ResourceLoopHead host pure program depth modes live test step env
    initialRemaining initialIndex initialState initialWorld remaining index state world trace spent fits)
    {restTrace : List Event} {outcome : Outcome type.denote} {final : World}
    {restSpent : Nat} {restFits : Bool}
    (execution : ResourceLoopExec host pure program depth modes live test step env
      remaining index state world restTrace outcome final restSpent restFits) :
    ResourceLoopExec host pure program depth modes live test step env
      initialRemaining initialIndex initialState initialWorld (trace ++ restTrace) outcome final
      (spent + restSpent) (fits && restFits) := by
  induction history generalizing restTrace outcome final restSpent restFits with
  | refl => simpa only [List.nil_append, Nat.zero_add, Bool.true_and] using execution
  | next history chosen stepRun ih =>
      have previous := ih (ResourceLoopExec.next chosen stepRun execution)
      simpa only [List.append_assoc, Nat.add_assoc, Bool.and_assoc] using previous

theorem transportPrefix (history : ResourceLoopHead host pure program depth modes live test step env
    initialRemaining initialIndex initialState initialWorld remaining index state world trace spent fits)
    {restTrace : List Event} {residual : Action type.denote} {final : World}
    {restSpent : Nat} {restFits : Bool}
    (progress : ResourceLoopPrefix host pure program depth modes live test step env
      remaining index state world restTrace residual final restSpent restFits) :
    ResourceLoopPrefix host pure program depth modes live test step env
      initialRemaining initialIndex initialState initialWorld (trace ++ restTrace) residual final
      (spent + restSpent) (fits && restFits) := by
  induction history generalizing restTrace residual final restSpent restFits with
  | refl => simpa only [List.nil_append, Nat.zero_add, Bool.true_and] using progress
  | next history chosen stepRun ih =>
      have previous := ih (ResourceLoopPrefix.next chosen stepRun progress)
      simpa only [List.append_assoc, Nat.add_assoc, Bool.and_assoc] using previous

theorem resources (history : ResourceLoopHead host pure program depth modes live test step env
    initialRemaining initialIndex initialState initialWorld remaining index state world trace spent fits)
    {budget : Nat} (bounded : LoopPrefixBound host pure program depth modes live test step env
      initialRemaining initialIndex initialState initialWorld budget) :
    spent ≤ budget ∧ fits = true := by
  have progress := history.transportPrefix (ResourceLoopPrefix.refl world remaining index state)
  obtain ⟨within, valid⟩ := bounded _ _ _ _ _ progress
  simpa only [Nat.add_zero, Bool.and_true] using And.intro within valid

theorem residualBound (history : ResourceLoopHead host pure program depth modes live test step env
    initialRemaining initialIndex initialState initialWorld remaining index state world trace spent fits)
    {budget : Nat} (bounded : LoopPrefixBound host pure program depth modes live test step env
      initialRemaining initialIndex initialState initialWorld budget) :
    LoopPrefixBound host pure program depth modes live test step env
      remaining index state world (budget - spent) := by
  intro restTrace residual final restSpent restFits progress
  obtain ⟨within, valid⟩ := bounded _ _ _ _ _ (history.transportPrefix progress)
  simp only [Bool.and_eq_true] at valid
  exact ⟨by omega, valid.2⟩

end ResourceLoopHead

end Verified.Wasi.Resource
