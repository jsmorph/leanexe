import Verified.Wasi.ResourcePrefix

/-! Compositional bounds on the resource semantics of effect commands.  `Bounded` states that every
run and every prefix of a command spends at most a budget and finds its frames, and `Rule` gives,
for each form of command, the facts about its parts from which that follows.  A bound on an effect
function's body follows by `bounded_of_rule` at each command. -/

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

/-- Some run of `command` returns `value`. -/
def Returns {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) (command : Command pureSigs effectSigs context result) (env : Env context)
    (value : result.denote) : Prop :=
  ∃ world trace final spent fits,
    ResourceExec host pure program depth modes live command env world trace (.returned value) final
      spent fits

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
        (∀ value, Returns host pure program depth modes (bindLive intermediate next live) first env
            value →
          Bounded host pure program depth (bindModes intermediate modes)
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
    obtain ⟨nextCost, nextFits⟩ :=
      (nextBound _ ⟨_, _, _, _, _, firstRun⟩).1 _ _ _ _ _ _ nextRun
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
    obtain ⟨nextCost, nextFits⟩ :=
      (nextBound _ ⟨_, _, _, _, _, firstRun⟩).2 _ _ _ _ _ _ progress
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

/-- The facts about a call's parts from which every run and every prefix of it spends at most
`budget` and finds its frames: for the first function, a frame at the call's depth and a bound on
its body, and for a later one, a bound on the call in the rest of the program. -/
def CallBoundRule {World : Type} (host : Host World) (pure : PureContext pureSigs) :
    {effectSigs : List EffectSig} → (program : EffectProg pureSigs effectSigs) →
    {signature : EffectSig} → EffectVar effectSigs signature → UInt64 → Env signature.params →
    Nat → Bool → Nat → Prop
  | _, .cons function rest, _, .here, depth, env, spent, fits, budget =>
      entryFits depth = true →
      Bounded host pure rest depth (entryModes function.params function.modes) (fun _ => false)
        function.body env budget → spent ≤ budget ∧ fits = true
  | _, .cons _ rest, _, .there callee, depth, env, spent, fits, budget =>
      CallBounded host pure rest callee depth env budget → spent ≤ budget ∧ fits = true
  | _, _, _, _, _, _, _, _, _ => True

theorem call_exec_bound_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world trace outcome final spent fits} (budget : Nat)
    (execution : ResourceCall host pure program callee depth env world trace outcome final spent
      fits) :
    CallBoundRule host pure program callee depth env spent fits budget := by
  cases execution with
  | here execution =>
    intro valid bounded
    obtain ⟨cost, fits⟩ := bounded.1 _ _ _ _ _ _ execution
    exact ⟨cost, by simp only [valid, fits, Bool.true_and]⟩
  | there execution =>
    intro bounded
    exact bounded.1 _ _ _ _ _ _ execution

theorem call_prefix_bound_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {world trace residual final spent fits} (budget : Nat)
    (progress : ResourceCallPrefix host pure program callee depth env world trace residual final
      spent fits) :
    CallBoundRule host pure program callee depth env spent fits budget := by
  cases progress with
  | guard program callee depth env world =>
    cases program with
    | nil => exact nomatch callee
    | cons function rest =>
      cases callee with
      | here => exact fun valid _ => ⟨Nat.zero_le _, valid⟩
      | there callee =>
        intro bounded
        exact ⟨Nat.zero_le _, (bounded.2 world _ _ _ _ _ (.guard rest callee depth env world)).2⟩
  | here progress =>
    intro valid bounded
    obtain ⟨cost, fits⟩ := bounded.2 _ _ _ _ _ _ progress
    exact ⟨cost, by simp only [valid, fits, Bool.true_and]⟩
  | there progress =>
    intro bounded
    exact bounded.2 _ _ _ _ _ _ progress

theorem callBounded_of_rule {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {budget : Nat}
    (applyRule : ∀ spent fits, CallBoundRule host pure program callee depth env spent fits budget →
      spent ≤ budget ∧ fits = true) :
    CallBounded host pure program callee depth env budget :=
  ⟨fun _ _ _ _ _ _ execution => applyRule _ _ (call_exec_bound_rule budget execution),
    fun _ _ _ _ _ _ progress => applyRule _ _ (call_prefix_bound_rule budget progress)⟩

theorem callBounded_here {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {depth : UInt64} {env : Env function.params} {budget : Nat}
    (valid : entryFits depth = true)
    (bounded : Bounded host pure rest depth (entryModes function.params function.modes)
      (fun _ => false) function.body env budget) :
    CallBounded host pure (.cons function rest) .here depth env budget :=
  callBounded_of_rule fun _ _ rule => rule valid bounded

theorem callBounded_there {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {function : EffectFunc pureSigs effectSigs} {rest : EffectProg pureSigs effectSigs}
    {signature : EffectSig} {callee : EffectVar effectSigs signature} {depth : UInt64}
    {env : Env signature.params} {budget : Nat}
    (bounded : CallBounded host pure rest callee depth env budget) :
    CallBounded host pure (.cons function rest) (.there callee) depth env budget :=
  callBounded_of_rule fun _ _ rule => rule bounded

theorem CallBounded.mono {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {signature : EffectSig}
    {callee : EffectVar effectSigs signature} {depth : UInt64} {env : Env signature.params}
    {budget budget' : Nat} (bounded : CallBounded host pure program callee depth env budget)
    (le : budget ≤ budget') : CallBounded host pure program callee depth env budget' :=
  ⟨fun _ _ _ _ _ _ execution => by
      obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ execution
      exact ⟨by omega, valid⟩,
    fun _ _ _ _ _ _ progress => by
      obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ _ progress
      exact ⟨by omega, valid⟩⟩

/-- What a run that returns a value tells of it: a read returns at most its capacity's bytes. -/
def ReadReturns (pure : PureContext pureSigs) {context : List Ty} {result : ResultTy}
    (command : Command pureSigs effectSigs context result)
    (env : Env context) (outcome : Outcome result.denote) : Prop :=
  match command, outcome with
  | .read capacity, .returned value => value.2.data.size ≤ (capacity.denote pure.funs env).toNat
  | _, _ => True

theorem exec_readReturns {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits}
    (run : ResourceExec host pure program depth modes live command env world trace outcome final
      spent fits) : ReadReturns pure command env outcome := by
  cases run with
  | read _ _ _ _ capacity env execution =>
    change Exec host (.read (capacity.denote pure.funs env) fun result =>
      .pure (result.errno, result.bytes)) _ _ _ _ at execution
    cases execution with
    | read_reject _ continuation =>
      cases continuation
      exact Nat.zero_le _
    | read_return _ operation continuation =>
      cases continuation
      have bound := (host.read_bound operation).1
      simp only [ReadReturns, readResult]
      split
      · exact bound
      · exact Nat.zero_le _
    | read_trap => trivial
  | _ => trivial

/-- A read returns at most its capacity's bytes. -/
theorem Returns.read_size {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {capacity : Expr pureSigs context .word} {env : Env context}
    {value : (Ty.pair .word .bytes).denote}
    (returns : Returns host pure program depth modes live (.read capacity) env value) :
    value.2.data.size ≤ (capacity.denote pure.funs env).toNat := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact exec_readReturns run

end Verified.Wasi.Resource
