import Verified.Wasi.ResourcePrefix

/-! Compositional bounds on the resource semantics of effect commands.  `Bounded` states that every
run and every prefix of a command spends at most a budget and finds its frames, and `Rule` gives,
for each form of command, the facts about its parts from which that follows.  A bound on an effect
function's body follows by `bounded_of_rule` at each command, and `callBounded_here` turns it into
a bound on a call of the function. -/

namespace Verified.Wasi.Resource

open LeanExe.Wasi

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

/-- Every run and every prefix of a call of `callee` at `depth` on `env` spends at most `budget`
and finds its frames. -/
def CallBounded {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) {signature : EffectSig}
    (callee : EffectVar effectSigs signature) (depth : UInt64) (env : Env signature.params)
    (budget : Nat) : Prop :=
  (∀ world trace outcome final spent fits,
    ResourceCall host pure program callee depth env world trace outcome final spent fits →
      spent ≤ budget ∧ fits = true) ∧
  ∀ world, CallPrefixBound host pure program callee depth env world budget

def Rule {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) {context result}
    (command : Command pureSigs effectSigs context result) (env : Env context)
    (spent : Nat) (fits : Bool) (budget : Nat) : Prop :=
  let conclusion := spent ≤ budget ∧ fits = true
  match command with
  | .unit => conclusion
  | .ret value => pure.ownedCost depth modes live value env ≤ budget →
      pure.exprFits depth value env = true → conclusion
  | .read capacity => pure.readCost depth modes live capacity env ≤ budget →
      pure.exprFits depth capacity env = true → conclusion
  | .write _ _ => conclusion
  | .exit code => pure.exprCost depth modes live code env ≤ budget →
      pure.exprFits depth code env = true → conclusion
  | .bind (intermediate := intermediate) first next =>
      ∀ firstBudget nextBudget, firstBudget + nextBudget ≤ budget →
        Bounded host pure program depth modes (bindLive intermediate next live) first env firstBudget →
        (∀ value, Bounded host pure program depth (bindModes intermediate modes)
          (shift intermediate.bindCount live) next (intermediate.bindEnv value env) nextBudget) →
        conclusion
  | .ite condition yes no =>
      ∀ yesBudget noBudget,
        pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env +
            (if condition.denote pure.funs env = true then yesBudget else noBudget) ≤ budget →
        pure.exprFits depth condition env = true →
        (condition.denote pure.funs env = true →
          Bounded host pure program depth modes live yes env yesBudget) →
        (condition.denote pure.funs env = false →
          Bounded host pure program depth modes live no env noBudget) →
        conclusion
  | .call (signature := signature) callee args =>
      ∀ calleeBudget, pure.argumentCost depth modes live signature args env + calleeBudget ≤ budget →
        pure.argumentFits depth args env = true →
        CallBounded host pure program callee (depth + 1)
          (Env.ofFn fun i => (args i).denote pure.funs env) calleeBudget →
        conclusion
  | .loop count initial test step =>
      ∀ loopBudget, pure.loopInitCost depth modes live count initial test step env + loopBudget ≤ budget →
        pure.loopInitFits depth count initial env = true →
        LoopBounded host pure program depth modes live test step env
          (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env) loopBudget → conclusion

theorem exec_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits} (budget : Nat)
    (execution : ResourceExec host pure program depth modes live command env world trace outcome final spent fits) :
    Rule host pure program depth modes live command env spent fits budget := by
  cases execution with
  | unit => exact ⟨Nat.zero_le _, rfl⟩
  | ret => exact fun cost valid => ⟨cost, valid⟩
  | read => exact fun cost valid => ⟨cost, valid⟩
  | write => exact ⟨Nat.zero_le _, rfl⟩
  | exit => exact fun cost valid => ⟨cost, valid⟩
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
  | ite_yes chosen execution =>
    intro yesBudget noBudget total conditionFits yesBound _
    obtain ⟨cost, valid⟩ := (yesBound chosen).1 _ _ _ _ _ _ execution
    rw [ite_eq_left chosen] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | ite_no chosen execution =>
    intro yesBudget noBudget total conditionFits _ noBound
    obtain ⟨cost, valid⟩ := (noBound chosen).1 _ _ _ _ _ _ execution
    rw [ite_eq_right (by simp [chosen])] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | call execution =>
    intro calleeBudget total argumentFits bounded
    obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ execution
    exact ⟨by omega, by simp only [argumentFits, valid, Bool.true_and]⟩
  | loop execution =>
    intro loopBudget total initFits bounded
    obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ execution
    exact ⟨by omega, by simp only [initFits, valid, Bool.true_and]⟩

theorem prefix_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final spent fits} (budget : Nat)
    (progress : ResourcePrefix host pure program depth modes live command env world trace residual final spent fits) :
    Rule host pure program depth modes live command env spent fits budget := by
  cases progress with
  | refl =>
    cases command <;> simp only [Rule] <;> intros <;> exact ⟨Nat.zero_le _, by trivial⟩
  | ret_charge => exact fun cost valid => ⟨cost, valid⟩
  | read_charge => exact fun cost valid => ⟨cost, valid⟩
  | exit_charge => exact fun cost valid => ⟨cost, valid⟩
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
  | ite_charge =>
    intro yesBudget noBudget total conditionFits _ _
    exact ⟨by omega, conditionFits⟩
  | ite_yes chosen progress =>
    intro yesBudget noBudget total conditionFits yesBound _
    obtain ⟨cost, valid⟩ := (yesBound chosen).2 _ _ _ _ _ _ progress
    rw [ite_eq_left chosen] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | ite_no chosen progress =>
    intro yesBudget noBudget total conditionFits _ noBound
    obtain ⟨cost, valid⟩ := (noBound chosen).2 _ _ _ _ _ _ progress
    rw [ite_eq_right (by simp [chosen])] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | call progress =>
    intro calleeBudget total argumentFits bounded
    obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ _ progress
    exact ⟨by omega, by simp only [argumentFits, valid, Bool.true_and]⟩
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

theorem bounded_of_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context} {budget : Nat}
    (applyRule : ∀ spent fits, Rule host pure program depth modes live command env spent fits budget →
      spent ≤ budget ∧ fits = true) : Bounded host pure program depth modes live command env budget :=
  ⟨fun _ _ _ _ _ _ execution => applyRule _ _ (exec_rule budget execution),
    fun _ _ _ _ _ _ progress => applyRule _ _ (prefix_rule budget progress)⟩

theorem Bounded.mono {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context} {budget budget' : Nat}
    (bounded : Bounded host pure program depth modes live command env budget) (le : budget ≤ budget') :
    Bounded host pure program depth modes live command env budget' :=
  ⟨fun _ _ _ _ _ _ execution => by
      obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ execution
      exact ⟨by omega, valid⟩,
    fun _ _ _ _ _ _ progress => by
      obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ _ progress
      exact ⟨by omega, valid⟩⟩

theorem word_readCost (pure : PureContext pureSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (capacity : UInt64) (env : Env context) :
    pure.readCost depth modes live (.word capacity) env = Verified.Wasi.readCost capacity := by
  simp only [PureContext.readCost, PureContext.exprCost, Expr.allocs, Expr.denote, Nat.zero_add]

/-- A call of the first function of a program, whose body is bounded and whose depth leaves room
for its frame, is bounded. -/
theorem callBounded_here {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {depth : UInt64} {env : Env function.params} {budget : Nat}
    (valid : entryFits depth = true)
    (body : Bounded host pure rest depth (entryModes function.params function.modes) (fun _ => false)
      function.body env budget) :
    CallBounded host pure (.cons function rest) .here depth env budget := by
  refine ⟨fun world trace outcome final spent fits execution => ?_,
    fun world trace residual final spent fits progress => ?_⟩
  · cases execution with
    | here execution =>
      obtain ⟨cost, bodyFits⟩ := body.1 _ _ _ _ _ _ execution
      exact ⟨cost, by simp only [valid, bodyFits, Bool.true_and]⟩
  · cases progress with
    | guard => exact ⟨Nat.zero_le _, valid⟩
    | here progress =>
      obtain ⟨cost, bodyFits⟩ := body.2 _ _ _ _ _ _ progress
      exact ⟨cost, by simp only [valid, bodyFits, Bool.true_and]⟩

/-- A bounded call of a function of the rest of a program is bounded in the whole program. -/
theorem callBounded_there {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {signature : EffectSig} {callee : EffectVar effectSigs signature}
    {depth : UInt64} {env : Env signature.params} {budget : Nat}
    (bounded : CallBounded host pure rest callee depth env budget) :
    CallBounded host pure (.cons function rest) (.there callee) depth env budget := by
  refine ⟨fun world trace outcome final spent fits execution => ?_,
    fun world trace residual final spent fits progress => ?_⟩
  · cases execution with
    | there execution => exact bounded.1 _ _ _ _ _ _ execution
  · cases progress with
    | guard => exact bounded.2 world _ _ _ _ _ (.guard rest callee depth env world)
    | there progress => exact bounded.2 _ _ _ _ _ _ progress

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

end Verified.Wasi.Resource
