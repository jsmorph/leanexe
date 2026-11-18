import Verified.Wasi.ResourceRules

/-! Bounds on the resource semantics of effect commands from one world.  `Bounded` bounds every run
and every prefix of a command from every world, which suits a command whose charge does not depend
on the host's replies.  `BoundedAt` bounds the runs and prefixes from one world, and `RuleAt` gives,
for a `bind`, an `ite`, a call, and a loop, the facts from which that follows, with the second
command of a `bind` bounded from the world in which the first returned.  A command whose charge
depends on the replies, such as a loop of writes whose passes depend on the counts that the writes
return, takes its bound from facts about the worlds that its runs reach: `boundedAt_of_rule` at
each of those four forms, and `Bounded.at` for the commands whose charge depends on no reply. -/

namespace Verified.Wasi.Resource

open LeanExe.Wasi

/-- Every run and every prefix of `command` from `world` uses at most `budget` and has enough
frames. -/
def BoundedAt {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (command : Command pureSigs effectSigs context result)
    (env : Env context) (world : World) (budget : Nat) : Prop :=
  (∀ trace outcome final spent fits,
    ResourceExec host pure program depth modes live command env world trace outcome final spent
      fits → spent ≤ budget ∧ fits = true) ∧
  PrefixBound host pure program depth modes live command env world budget

/-- Every run and every prefix of a loop's passes from `world` uses at most `budget` and has enough
frames. -/
def LoopBoundedAt {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) (remaining index : Nat) (state : type.denote) (world : World)
    (budget : Nat) : Prop :=
  (∀ trace outcome final spent fits,
    ResourceLoopExec host pure program depth modes live test step env remaining index state
      world trace outcome final spent fits → spent ≤ budget ∧ fits = true) ∧
  LoopPrefixBound host pure program depth modes live test step env remaining index state world
    budget

/-- Every run and every prefix of a call of `callee` from `world` uses at most `budget` and has
enough frames. -/
def CallBoundedAt {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) {signature : EffectSig}
    (callee : EffectVar effectSigs signature) (depth : UInt64) (env : Env signature.params)
    (world : World) (budget : Nat) : Prop :=
  (∀ trace outcome final spent fits,
    ResourceCall host pure program callee depth env world trace outcome final spent fits →
      spent ≤ budget ∧ fits = true) ∧
  CallPrefixBound host pure program callee depth env world budget

theorem Bounded.at {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context} {budget : Nat}
    (bounded : Bounded host pure program depth modes live command env budget) (world : World) :
    BoundedAt host pure program depth modes live command env world budget :=
  ⟨fun _ _ _ _ _ execution => bounded.1 _ _ _ _ _ _ execution, bounded.2 world⟩

theorem BoundedAt.mono {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context} {world : World}
    {budget budget' : Nat}
    (bounded : BoundedAt host pure program depth modes live command env world budget)
    (le : budget ≤ budget') :
    BoundedAt host pure program depth modes live command env world budget' :=
  ⟨fun _ _ _ _ _ execution => by
      obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ execution
      exact ⟨by omega, valid⟩,
    fun _ _ _ _ _ progress => by
      obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ progress
      exact ⟨by omega, valid⟩⟩

/-- The facts about a command's parts from which every run and every prefix of it from `world`
uses at most `budget` and has enough frames: for a `bind`, `ite`, call, or loop, bounds on its
parts from the worlds in which they start, and for any other command, `Rule`. -/
def RuleAt {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) {context result}
    (command : Command pureSigs effectSigs context result) (env : Env context) (world : World)
    (spent : Nat) (fits : Bool) (budget : Nat) : Prop :=
  let conclusion := spent ≤ budget ∧ fits = true
  match command with
  | .bind (intermediate := intermediate) first next =>
      ∀ firstBudget nextBudget, firstBudget + nextBudget ≤ budget →
        BoundedAt host pure program depth modes (bindLive intermediate next live) first env world
          firstBudget →
        (∀ trace value after firstSpent firstFits,
          ResourceExec host pure program depth modes (bindLive intermediate next live) first env
            world trace (.returned value) after firstSpent firstFits →
          BoundedAt host pure program depth (bindModes intermediate modes)
            (shift intermediate.bindCount live) next (intermediate.bindEnv value env) after
            nextBudget) →
        conclusion
  | .ite condition yes no =>
      ∀ yesBudget noBudget,
        pure.exprCost depth modes (fun i => live i || yes.uses i || no.uses i) condition env +
            (if condition.denote pure.funs env = true then yesBudget else noBudget) ≤ budget →
        pure.exprFits depth condition env = true →
        (condition.denote pure.funs env = true →
          BoundedAt host pure program depth modes live yes env world yesBudget) →
        (condition.denote pure.funs env = false →
          BoundedAt host pure program depth modes live no env world noBudget) →
        conclusion
  | .call (signature := signature) callee args =>
      ∀ calleeBudget, pure.argumentCost depth modes live signature args env + calleeBudget ≤ budget →
        pure.argumentFits depth args env = true →
        CallBoundedAt host pure program callee (depth + 1)
          (Env.ofFn fun i => (args i).denote pure.funs env) world calleeBudget →
        conclusion
  | .loop count initial test step =>
      ∀ loopBudget,
        pure.loopInitCost depth modes live count initial test step env + loopBudget ≤ budget →
        pure.loopInitFits depth count initial env = true →
        LoopBoundedAt host pure program depth modes live test step env
          (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env) world loopBudget →
        conclusion
  | command => Rule host pure program depth modes live command env spent fits budget

theorem exec_rule_at {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits} (budget : Nat)
    (execution : ResourceExec host pure program depth modes live command env world trace outcome
      final spent fits) :
    RuleAt host pure program depth modes live command env world spent fits budget := by
  have rule := exec_rule budget execution
  cases execution with
  | bind_return firstRun nextRun =>
    intro firstBudget nextBudget total firstBound nextBound
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ firstRun
    obtain ⟨nextCost, nextFits⟩ := (nextBound _ _ _ _ _ firstRun).1 _ _ _ _ _ nextRun
    exact ⟨by omega, by simp only [firstFits, nextFits, Bool.true_and]⟩
  | bind_exit firstRun =>
    intro firstBudget nextBudget total firstBound _
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ firstRun
    exact ⟨by omega, firstFits⟩
  | bind_trap firstRun =>
    intro firstBudget nextBudget total firstBound _
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ firstRun
    exact ⟨by omega, firstFits⟩
  | ite_yes chosen execution =>
    intro yesBudget noBudget total conditionFits yesBound _
    obtain ⟨cost, valid⟩ := (yesBound chosen).1 _ _ _ _ _ execution
    rw [ite_eq_left chosen] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | ite_no chosen execution =>
    intro yesBudget noBudget total conditionFits _ noBound
    obtain ⟨cost, valid⟩ := (noBound chosen).1 _ _ _ _ _ execution
    rw [ite_eq_right (by simp [chosen])] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | call execution =>
    intro calleeBudget total argumentFits bounded
    obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ execution
    exact ⟨by omega, by simp only [argumentFits, valid, Bool.true_and]⟩
  | loop execution =>
    intro loopBudget total initFits bounded
    obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ execution
    exact ⟨by omega, by simp only [initFits, valid, Bool.true_and]⟩
  | unit => exact rule
  | ret => exact rule
  | read => exact rule
  | readAll => exact rule
  | write => exact rule
  | exit => exact rule
  | sys => exact rule

theorem prefix_rule_at {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace residual final spent fits} (budget : Nat)
    (progress : ResourcePrefix host pure program depth modes live command env world trace residual
      final spent fits) :
    RuleAt host pure program depth modes live command env world spent fits budget := by
  have rule := prefix_rule budget progress
  cases progress with
  | refl =>
    cases command <;> first
      | exact rule
      | (repeat intro _
         exact ⟨Nat.zero_le _, rfl⟩)
  | returned execution => exact exec_rule_at budget execution
  | bind_left progress =>
    intro firstBudget nextBudget total firstBound _
    obtain ⟨cost, valid⟩ := firstBound.2 _ _ _ _ _ progress
    exact ⟨by omega, valid⟩
  | bind_right firstRun progress =>
    intro firstBudget nextBudget total firstBound nextBound
    obtain ⟨firstCost, firstFits⟩ := firstBound.1 _ _ _ _ _ firstRun
    obtain ⟨nextCost, nextFits⟩ := (nextBound _ _ _ _ _ firstRun).2 _ _ _ _ _ progress
    exact ⟨by omega, by simp only [firstFits, nextFits, Bool.true_and]⟩
  | ite_charge =>
    intro yesBudget noBudget total conditionFits _ _
    exact ⟨by omega, conditionFits⟩
  | ite_yes chosen progress =>
    intro yesBudget noBudget total conditionFits yesBound _
    obtain ⟨cost, valid⟩ := (yesBound chosen).2 _ _ _ _ _ progress
    rw [ite_eq_left chosen] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | ite_no chosen progress =>
    intro yesBudget noBudget total conditionFits _ noBound
    obtain ⟨cost, valid⟩ := (noBound chosen).2 _ _ _ _ _ progress
    rw [ite_eq_right (by simp [chosen])] at total
    exact ⟨by omega, by simp only [conditionFits, valid, Bool.true_and]⟩
  | call progress =>
    intro calleeBudget total argumentFits bounded
    obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ progress
    exact ⟨by omega, by simp only [argumentFits, valid, Bool.true_and]⟩
  | loop progress =>
    intro loopBudget total initFits bounded
    obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ progress
    exact ⟨by omega, by simp only [initFits, valid, Bool.true_and]⟩
  | loop_count =>
    intro loopBudget total initFits _
    dsimp only [PureContext.loopInitCost] at total
    simp only [PureContext.loopInitFits, Bool.and_eq_true] at initFits
    exact ⟨by omega, initFits.1⟩
  | loop_init =>
    intro loopBudget total initFits _
    exact ⟨by omega, initFits⟩
  | ret_charge => exact rule
  | read_charge => exact rule
  | readAll => exact rule
  | exit_charge => exact rule
  | sys => exact rule

theorem boundedAt_of_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context} {world : World}
    {budget : Nat}
    (applyRule : ∀ spent fits,
      RuleAt host pure program depth modes live command env world spent fits budget →
        spent ≤ budget ∧ fits = true) :
    BoundedAt host pure program depth modes live command env world budget :=
  ⟨fun _ _ _ _ _ execution => applyRule _ _ (exec_rule_at budget execution),
    fun _ _ _ _ _ progress => applyRule _ _ (prefix_rule_at budget progress)⟩

/-- The facts about a call's parts from which every run and every prefix of it from `world` uses at
most `budget` and has enough frames: for the first function, a frame at the call's depth and a
bound on its body from `world`, and for a later one, a bound on the call in the rest of the
program from `world`. -/
def CallRuleAt {World : Type} (host : Host World) (pure : PureContext pureSigs) (world : World) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    {signature : EffectSig} → EffectVar effectSigs signature → UInt64 → Env signature.params →
    Nat → Bool → Nat → Prop
  | _, .cons function rest, _, .here, depth, env, spent, fits, budget =>
      entryFits depth = true →
      BoundedAt host pure rest depth (entryModes function.params function.modes) (fun _ => false)
        function.body env world budget → spent ≤ budget ∧ fits = true
  | _, .cons _ rest, _, .there callee, depth, env, spent, fits, budget =>
      CallBoundedAt host pure rest callee depth env world budget → spent ≤ budget ∧ fits = true
  | _, _, _, _, _, _, _, _, _ => True

theorem call_exec_rule_at {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world trace outcome final spent fits} (budget : Nat)
    (execution : ResourceCall host pure program callee depth env world trace outcome final spent
      fits) :
    CallRuleAt host pure world program callee depth env spent fits budget := by
  cases execution with
  | here execution =>
    intro valid bounded
    obtain ⟨cost, fits⟩ := bounded.1 _ _ _ _ _ execution
    exact ⟨cost, by simp only [valid, fits, Bool.true_and]⟩
  | there execution =>
    intro bounded
    exact bounded.1 _ _ _ _ _ execution

theorem call_prefix_rule_at {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world trace residual final spent fits} (budget : Nat)
    (progress : ResourceCallPrefix host pure program callee depth env world trace residual final
      spent fits) :
    CallRuleAt host pure world program callee depth env spent fits budget := by
  cases progress with
  | guard program callee depth env world =>
    cases program with
    | nil => exact nomatch callee
    | cons function rest =>
      cases callee with
      | here => exact fun valid _ => ⟨Nat.zero_le _, valid⟩
      | there callee =>
        intro bounded
        exact ⟨Nat.zero_le _, (bounded.2 _ _ _ _ _ (.guard rest callee depth env world)).2⟩
  | here progress =>
    intro valid bounded
    obtain ⟨cost, fits⟩ := bounded.2 _ _ _ _ _ progress
    exact ⟨cost, by simp only [valid, fits, Bool.true_and]⟩
  | there progress =>
    intro bounded
    exact bounded.2 _ _ _ _ _ progress

theorem callBoundedAt_here {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {depth : UInt64} {env : Env function.params} {world : World} {budget : Nat}
    (valid : entryFits depth = true)
    (bounded : BoundedAt host pure rest depth (entryModes function.params function.modes)
      (fun _ => false) function.body env world budget) :
    CallBoundedAt host pure (.cons function rest) .here depth env world budget :=
  ⟨fun _ _ _ _ _ execution => call_exec_rule_at budget execution valid bounded,
    fun _ _ _ _ _ progress => call_prefix_rule_at budget progress valid bounded⟩

end Verified.Wasi.Resource
