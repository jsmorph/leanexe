import Verified.Examples.WasiRetain
import Verified.Examples.WasiResourceRules

namespace Verified.Examples.WasiRetain

open LeanExe LeanExe.Wasi Verified Verified.Wasi Verified.Wasi.Resource
open Verified.Examples.WasiResourceRules

private def returnRead : Command [] []
    [.elem (.prod .word .word), .pair .word .bytes, .bytes, .word] (.value .bytes) :=
  .ret (.letPair (.var (.there .here)) (.var .here))

private def writePrevious : Command [] [] [.pair .word .bytes, .bytes, .word] (.value .bytes) :=
  .bind (.write .stdout (.there .here)) returnRead

private theorem returnRead_bounded {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (live : Nat → Bool)
    (env : Env [.elem (.prod .word .word), .pair .word .bytes, .bytes, .word]) :
    Bounded host pure .nil depth [.owned, .owned, .owned, .borrowed]
      (shift 1 (shift 1 live)) returnRead env 0 := by
  apply bounded_of_rule
  intro spent fits rule
  exact rule (by change 0 ≤ 0; omega) rfl

private theorem writePrevious_bounded {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (live : Nat → Bool) (env : Env [.pair .word .bytes, .bytes, .word]) :
    Bounded host pure .nil depth [.owned, .owned, .borrowed]
      (shift 1 live) writePrevious env 0 := by
  apply bounded_of_rule
  intro spent fits rule
  apply rule 0 0 (by omega)
  · apply bounded_of_rule
    intro spent fits rule
    exact rule
  · intro value
    exact returnRead_bounded host pure depth live _

private theorem step_bounded {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (live : Nat → Bool) (env : Env [.bytes, .word]) :
    Bounded host pure .nil depth [.owned, .borrowed] live step env 56 := by
  apply bounded_of_rule
  intro spent fits rule
  apply rule 56 0 (by omega)
  · apply bounded_of_rule
    intro spent fits rule
    apply rule
    · rw [word_readCost]
      simp [Verified.Wasi.readCost, UInt64.reduceToNat, Verified.Bytes.allocationCost]
    · rfl
  · intro value
    exact writePrevious_bounded host pure depth live _

private theorem loop_exec_bound {World : Type} {host : Host World} {pure : PureContext []}
    {depth : UInt64} {live : Nat → Bool}
    {remaining index : Nat} {state : Bytes} {world final : World}
    {trace : List Event} {outcome : Outcome Bytes} {spent : Nat} {fits : Bool}
    (execution : ResourceLoopExec host pure .nil depth [] live (.bool true) step .nil
      remaining index state world trace outcome final spent fits) :
    spent ≤ remaining * 56 ∧ fits = true := by
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
    spent ≤ remaining * 56 ∧ fits = true := by
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
    (depth : UInt64) : Bounded host pure .nil depth [] (fun _ => false) body .nil 112 := by
  apply bounded_of_rule
  intro spent fits rule
  apply rule 112
  · change 0 + 112 ≤ 112
    omega
  · rfl
  · exact ⟨fun _ _ _ _ _ _ execution => loop_exec_bound execution,
      fun _ _ _ _ _ _ progress => loop_prefix_bound progress⟩

theorem body_prefix_bound {World : Type} (host : Host World) (pure : PureContext [])
    (depth : UInt64) (world : World) :
    PrefixBound host pure .nil depth [] (fun _ => false) body .nil world 112 :=
  (body_bounded host pure depth).2 world

theorem call_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host (.ofProg compiled.pure.program compiled.pure.funs)
      compiled.program compiled.retain.callee 0 .nil world 112 := by
  intro trace residual final spent fits progress
  exact call_prefix_rule 112 progress rfl (body_prefix_bound host _ 0 world)

end Verified.Examples.WasiRetain
