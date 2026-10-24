import Verified.Wasi.ResourcePrefix

namespace Verified.Examples.WasiResourceRules

open LeanExe.Wasi Verified Verified.Wasi Verified.Wasi.Resource

def Bounded {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (command : Command pureSigs effectSigs context result)
    (env : Env context) (budget : Nat) : Prop :=
  (∀ world trace outcome final spent fits,
    ResourceExec host pure program depth modes live command env world trace outcome final spent fits →
      spent ≤ budget ∧ fits = true) ∧
  ∀ world, PrefixBound host pure program depth modes live command env world budget

def LoopBounded {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) (remaining index : Nat) (state : type.denote) (budget : Nat) : Prop :=
  (∀ world trace outcome final spent fits,
    ResourceLoopExec host pure program depth modes live test step env remaining index state
      world trace outcome final spent fits → spent ≤ budget ∧ fits = true) ∧
  ∀ world, LoopPrefixBound host pure program depth modes live test step env remaining index state world budget

def Rule {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) {context result}
    (command : Command pureSigs effectSigs context result) (env : Env context)
    (spent : Nat) (fits : Bool) (budget : Nat) : Prop :=
  let conclusion := spent ≤ budget ∧ fits = true
  match command with
  | .ret value => pure.ownedCost depth modes live value env ≤ budget →
      pure.exprFits depth value env = true → conclusion
  | .read capacity => pure.readCost depth modes live capacity env ≤ budget →
      pure.exprFits depth capacity env = true → conclusion
  | .write _ _ => conclusion
  | .bind (intermediate := intermediate) first next =>
      ∀ firstBudget nextBudget, firstBudget + nextBudget ≤ budget →
        Bounded host pure program depth modes (bindLive intermediate next live) first env firstBudget →
        (∀ value, Bounded host pure program depth (bindModes intermediate modes)
          (shift intermediate.bindCount live) next (intermediate.bindEnv value env) nextBudget) →
        conclusion
  | .loop count initial test step =>
      ∀ loopBudget, pure.loopInitCost depth modes live count initial test step env + loopBudget ≤ budget →
        pure.loopInitFits depth count initial env = true →
        LoopBounded host pure program depth modes live test step env
          (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env) loopBudget → conclusion
  | _ => True

theorem exec_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits} (budget : Nat)
    (execution : ResourceExec host pure program depth modes live command env world trace outcome final spent fits) :
    Rule host pure program depth modes live command env spent fits budget := by
  cases execution with
  | ret => exact fun cost valid => ⟨cost, valid⟩
  | read => exact fun cost valid => ⟨cost, valid⟩
  | write => exact ⟨Nat.zero_le _, rfl⟩
  | bind_return firstRun nextRun =>
    intro firstBudget nextBudget total firstBound nextBound
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ _ firstRun
    obtain ⟨nextCost, nextFits⟩ := (nextBound _).1 _ _ _ _ _ _ nextRun
    exact ⟨by omega, by simp only [firstFits, nextFits, Bool.true_and]⟩
  | bind_exit firstRun =>
    intro firstBudget nextBudget total firstBound _
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ _ firstRun
    exact ⟨by omega, firstFits⟩
  | bind_trap firstRun =>
    intro firstBudget nextBudget total firstBound _
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ _ firstRun
    exact ⟨by omega, firstFits⟩
  | loop execution =>
    intro loopBudget total initFits bounded
    obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ execution
    exact ⟨by omega, by simp only [initFits, valid, Bool.true_and]⟩
  | _ => trivial

theorem prefix_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final spent fits} (budget : Nat)
    (progress : ResourcePrefix host pure program depth modes live command env world trace residual final spent fits) :
    Rule host pure program depth modes live command env spent fits budget := by
  cases progress with
  | refl =>
    cases command <;> simp only [Rule] <;> intros <;> exact ⟨Nat.zero_le _, True.intro⟩
  | ret_charge => exact fun cost valid => ⟨cost, valid⟩
  | read_charge => exact fun cost valid => ⟨cost, valid⟩
  | returned execution => exact exec_rule budget execution
  | bind_left progress =>
    intro firstBudget nextBudget total firstBound _
    obtain ⟨cost, valid⟩ := firstBound.2 _ _ _ _ _ _ progress
    exact ⟨by omega, valid⟩
  | bind_right firstRun progress =>
    intro firstBudget nextBudget total firstBound nextBound
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ _ firstRun
    obtain ⟨nextCost, nextFits⟩ := (nextBound _).2 _ _ _ _ _ _ progress
    exact ⟨by omega, by simp only [firstFits, nextFits, Bool.true_and]⟩
  | loop progress =>
    intro loopBudget total initFits bounded
    obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ _ progress
    exact ⟨by omega, by simp only [initFits, valid, Bool.true_and]⟩
  | loop_count =>
    intro loopBudget total initFits _
    dsimp only [PureContext.loopInitCost] at total
    simp only [PureContext.loopInitFits, Bool.and_eq_true] at initFits
    exact ⟨by omega, initFits.1⟩
  | loop_init =>
    intro loopBudget total initFits _
    exact ⟨by omega, initFits⟩
  | _ => trivial

theorem bounded_of_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context} {budget : Nat}
    (applyRule : ∀ spent fits, Rule host pure program depth modes live command env spent fits budget →
      spent ≤ budget ∧ fits = true) : Bounded host pure program depth modes live command env budget :=
  ⟨fun _ _ _ _ _ _ execution => applyRule _ _ (exec_rule budget execution),
    fun _ _ _ _ _ _ progress => applyRule _ _ (prefix_rule budget progress)⟩

theorem word_readCost (pure : PureContext pureSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (capacity : UInt64) (env : Env context) :
    pure.readCost depth modes live (.word capacity) env = Verified.Wasi.readCost capacity := by
  simp only [PureContext.readCost, PureContext.exprCost, Expr.allocs, Expr.denote, Nat.zero_add]

def CallRule {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (world : World) : {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    {signature : EffectSig} → EffectVar effectSigs signature → UInt64 → Env signature.params →
    Nat → Bool → Nat → Prop
  | _, .cons function rest, _, .here, depth, env, spent, fits, budget =>
      entryFits depth = true →
      PrefixBound host pure rest depth (entryModes function.params function.modes) (fun _ => false)
        function.body env world budget → spent ≤ budget ∧ fits = true
  | _, _, _, _, _, _, _, _, _ => True

theorem call_prefix_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world trace residual final spent fits} (budget : Nat)
    (progress : ResourceCallPrefix host pure program callee depth env world trace residual final spent fits) :
    CallRule host pure world program callee depth env spent fits budget := by
  cases progress with
  | guard program callee depth env world =>
    cases program with
    | nil => exact nomatch callee
    | cons function rest =>
      cases callee with
      | here => exact fun valid _ => ⟨Nat.zero_le _, valid⟩
      | there callee => trivial
  | here progress =>
    intro valid bounded
    obtain ⟨cost, fits⟩ := bounded _ _ _ _ _ progress
    exact ⟨cost, by simp only [valid, fits, Bool.true_and]⟩
  | there progress => trivial

end Verified.Examples.WasiResourceRules
