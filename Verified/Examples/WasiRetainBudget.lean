module

public import Verified.Examples.WasiRetain
public import Verified.Wasi.ResourceRules

@[expose] public section

namespace Verified.Examples.WasiRetain

open LeanExe LeanExe.Wasi Verified Verified.Wasi Verified.Wasi.Resource

/-- Closes a goal about the charge of an expression by unfolding the charge's definitions. -/
local macro "charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.loopTestCost, Expr.allocs, Var.cost, Expr.mode,
      coerceCost, Ty.copyCost, Expr.denote, loopEnv, loopModes, modeAt, sumBelow,
      UInt64.reduceToNat, Nat.add_zero, Nat.zero_add, ↓reduceIte, ite_self] <;>
   omega))

private theorem step_bounded {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (outer : Nat → Bool) (env : Env [.bytes, .word]) :
    Bounded host pure .nil depth [.owned, .borrowed] (shift 2 outer) step env 0 := by
  apply bounded_of_rule
  intro spent fits rule
  apply rule 0 0 (by omega)
  · apply bounded_of_rule
    intro spent fits rule
    apply rule 0 0 (by omega)
    · apply bounded_of_rule
      intro spent fits rule
      exact rule (by change 0 ≤ 0; omega) rfl
    · intro value _
      apply bounded_of_rule
      intro spent fits rule
      apply rule 0 0 (by omega)
      · apply bounded_of_rule
        intro spent fits rule
        exact rule (by change 0 ≤ 0; omega) rfl
      · intro value _
        apply bounded_of_rule
        intro spent fits rule
        exact rule
  · intro value _
    apply bounded_of_rule
    intro spent fits rule
    apply rule 0 0 (by omega)
    · apply bounded_of_rule
      intro spent fits rule
      apply rule 0 0 (by omega)
      · apply bounded_of_rule
        intro spent fits rule
        exact rule (by change 0 ≤ 0; omega) rfl
      · intro value _
        apply bounded_of_rule
        intro spent fits rule
        apply rule 0 0 (by omega)
        · apply bounded_of_rule
          intro spent fits rule
          exact rule (by change 0 ≤ 0; omega) rfl
        · intro value _
          apply bounded_of_rule
          intro spent fits rule
          exact rule (by change 0 ≤ 0; omega)
    · intro value _
      letPair_free
      apply bounded_of_rule
      intro spent fits rule
      exact rule (by change 0 ≤ 0; omega) rfl

private theorem loop_exec_bound {World : Type} {host : Host World} {pure : PureContext []}
    {depth : UInt64} {live : Nat → Bool}
    {remaining index : Nat} {state : Bytes} {world final : World}
    {trace : List Event} {outcome : Outcome Bytes} {spent : Nat} {fits : Bool}
    (execution : ResourceLoopExec host pure .nil depth [] live (.bool true) step .nil
      remaining index state world trace outcome final spent fits) :
    spent ≤ 0 ∧ fits = true := by
  induction remaining generalizing index state world trace outcome final spent fits with
  | zero => cases execution; exact ⟨by omega, rfl⟩
  | succ remaining ih =>
    cases execution with
    | stop _ chosen => exact Bool.noConfusion chosen
    | next chosen stepRun restRun =>
      obtain ⟨stepCost, stepFits⟩ := (step_bounded host pure depth _ _).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := ih restRun
      change 0 + _ + _ ≤ _ ∧ (true && _ && _) = true
      exact ⟨by omega, by simp only [stepFits, restFits, Bool.true_and]⟩
    | exit chosen stepRun =>
      obtain ⟨stepCost, stepFits⟩ := (step_bounded host pure depth _ _).1 _ _ _ _ _ _ stepRun
      change 0 + _ ≤ _ ∧ (true && _) = true
      exact ⟨by omega, by simp only [stepFits, Bool.true_and]⟩
    | trap chosen stepRun =>
      obtain ⟨stepCost, stepFits⟩ := (step_bounded host pure depth _ _).1 _ _ _ _ _ _ stepRun
      change 0 + _ ≤ _ ∧ (true && _) = true
      exact ⟨by omega, by simp only [stepFits, Bool.true_and]⟩

private theorem loop_prefix_bound {World : Type} {host : Host World} {pure : PureContext []}
    {depth : UInt64} {live : Nat → Bool}
    {remaining index : Nat} {state : Bytes} {world final : World}
    {trace : List Event} {residual : Action Bytes} {spent : Nat} {fits : Bool}
    (progress : ResourceLoopPrefix host pure .nil depth [] live (.bool true) step .nil
      remaining index state world trace residual final spent fits) :
    spent ≤ 0 ∧ fits = true := by
  induction remaining generalizing index state world trace residual final spent fits with
  | zero => cases progress with
    | refl => exact ⟨by omega, rfl⟩
    | returned execution => exact loop_exec_bound execution
  | succ remaining ih =>
    cases progress with
    | refl => exact ⟨by omega, rfl⟩
    | test_charge => change 0 ≤ _ ∧ true = true; exact ⟨by omega, rfl⟩
    | returned execution => exact loop_exec_bound execution
    | step chosen stepProgress =>
      obtain ⟨stepCost, stepFits⟩ := (step_bounded host pure depth _ _).2 _ _ _ _ _ _ stepProgress
      change 0 + _ ≤ _ ∧ (true && _) = true
      exact ⟨by omega, by simp only [stepFits, Bool.true_and]⟩
    | next chosen stepRun restProgress =>
      obtain ⟨stepCost, stepFits⟩ := (step_bounded host pure depth _ _).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := ih restProgress
      change 0 + _ + _ ≤ _ ∧ (true && _ && _) = true
      exact ⟨by omega, by simp only [stepFits, restFits, Bool.true_and]⟩

private theorem body_bounded {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) : Bounded host pure .nil depth [] (fun _ => false) body .nil 56 := by
  apply bounded_of_rule
  intro spent fits rule
  apply rule 0
  · charge
  · rfl
  · exact ⟨fun _ _ _ _ _ _ execution => loop_exec_bound execution,
      fun _ _ _ _ _ _ progress => loop_prefix_bound progress⟩

theorem body_prefix_bound {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (world : World) :
    PrefixBound host pure .nil depth [] (fun _ => false) body .nil world 56 :=
  (body_bounded host pure depth).2 world

theorem call_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host (.ofProg compiled.pure.program compiled.pure.funs)
      compiled.program compiled.retain.callee 0 .nil world 56 := by
  intro trace residual final spent fits progress
  exact call_prefix_rule 56 progress rfl (body_prefix_bound host _ 0 world)

end Verified.Examples.WasiRetain
