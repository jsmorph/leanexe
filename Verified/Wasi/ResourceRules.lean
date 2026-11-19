import Verified.Wasi.ResourcePrefix
import Verified.BoundFacts

/-! Compositional bounds on the resource semantics of effect commands.  `Bounded` states that every
run and every prefix of a command uses at most a budget and has enough frames, and `Rule` gives,
for each form of command, the facts about its parts from which that follows.  A bound on an effect
function's body follows by `bounded_of_rule` at each command, and `returns_fact` gives the values
that the parts of a command that returns compute (`ReturnFact`).  `loop_bounded` bounds a loop
whose passes each charge at most a constant from the states of an invariant that every pass keeps,
and `loop_bounded_sum` one whose pass at each index charges at most a charge of that index, by
their sum (`passSum`). -/

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

/-- Every run and every prefix of a call of `callee` at `depth` on `env` uses at most `budget`
and has enough frames. -/
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
  | .readAll limit => pure.readAllCost depth modes live limit env ≤ budget →
      pure.exprFits depth limit env = true → conclusion
  | .write _ _ _ _ => conclusion
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
  | .sys operation form args inputs buffers =>
      (∀ world trace outcome final, Exec host
        (form.runWith operation (args.map env.get) (inputs.map env.get) (buffers.map env.get))
          world trace outcome final →
        sysCost form operation trace + pure.sysTakeCost depth modes live args inputs buffers env ≤
          budget) →
      (∀ world trace residual final, Prefix host
        (form.runWith operation (args.map env.get) (inputs.map env.get) (buffers.map env.get))
          world trace residual final →
        sysCost form operation trace + pure.sysTakeCost depth modes live args inputs buffers env ≤
          budget) →
      conclusion
  | .letPair pair body =>
      ∀ bodyBudget, letPairCost modes live pair body env + bodyBudget ≤ budget →
        Bounded host pure program depth (letPairModes pair modes) (shift 2 live) body
          (letPairEnv pair env) bodyBudget →
        conclusion

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
  | readAll => exact fun cost valid => ⟨cost, valid⟩
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
  | sys execution => exact fun bound _ => ⟨bound _ _ _ _ execution, rfl⟩
  | letPair execution =>
    intro bodyBudget total bounded
    obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ execution
    exact ⟨by omega, valid⟩

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
  | readAll => exact fun cost valid => ⟨cost, valid⟩
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
  | sys progress => exact fun _ bound => ⟨bound _ _ _ _ progress, rfl⟩
  | letPair progress =>
    intro bodyBudget total bounded
    obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ _ progress
    exact ⟨by omega, valid⟩

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

/-- A `letPair` is bounded by its charge before the body and a bound on its body. -/
theorem Bounded.letPair {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {pair : Var context (.pair first second)}
    {body : Command pureSigs effectSigs (second :: first :: context) result} {env : Env context}
    {bodyBudget budget : Nat} (cost : letPairCost modes live pair body env + bodyBudget ≤ budget)
    (bounded : Bounded host pure program depth (letPairModes pair modes) (shift 2 live) body
      (letPairEnv pair env) bodyBudget) :
    Bounded host pure program depth modes live (.letPair pair body) env budget :=
  bounded_of_rule fun _ _ rule => rule bodyBudget cost bounded

/-- A `letPair` that charges nothing before its body, one of a borrowed pair or of a pair that dies
there, is bounded by a bound on its body. -/
theorem Bounded.letPair_free {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {pair : Var context (.pair first second)}
    {body : Command pureSigs effectSigs (second :: first :: context) result} {env : Env context}
    {budget : Nat} (free : letPairCost modes live pair body env = 0)
    (bounded : Bounded host pure program depth (letPairModes pair modes) (shift 2 live) body
      (letPairEnv pair env) budget) :
    Bounded host pure program depth modes live (.letPair pair body) env budget :=
  Bounded.letPair (by omega) bounded

/-- Reduces `Bounded` of each `letPair` at the head of a command to `Bounded` of its body, for a
pair that is borrowed or that dies at the `letPair`, which `rfl` shows by reducing the pair's mode
or its liveness. -/
macro "letPair_free" : tactic => `(tactic|
  repeat (refine Verified.Wasi.Resource.Bounded.letPair_free (by
    first
      | exact Verified.Wasi.Resource.letPairCost_borrowed rfl
      | exact Verified.Wasi.Resource.letPairCost_dead rfl) ?_))

/-- What a run of a `letPair` that returns a value gives: a run of its body that returns it. -/
private def LetPairReturn {World : Type} (host : Host World) (pure : PureContext pureSigs)
    (program : EffectProg pureSigs effectSigs) (depth : UInt64) (modes : List Mode)
    (live : Nat → Bool) : {context : List Ty} → {result : ResultTy} →
      Command pureSigs effectSigs context result → Env context → Outcome result.denote → Prop
  | _, _, .letPair pair body, env, .returned value =>
    Returns host pure program depth (letPairModes pair modes) (shift 2 live) body
      (letPairEnv pair env) value
  | _, _, _, _, _ => True

private theorem letPairReturn {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth modes live context result}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits}
    (run : ResourceExec host pure program depth modes live command env world trace outcome final
      spent fits) :
    LetPairReturn host pure program depth modes live command env outcome := by
  cases run with
  | letPair execution =>
    cases outcome with
    | returned value => exact ⟨_, _, _, _, _, execution⟩
    | exited => trivial
    | trapped => trivial
  | _ => trivial

/-- A run of a `letPair` that returns a value is a run of its body that returns it. -/
theorem Returns.letPair {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {pair : Var context (.pair first second)}
    {body : Command pureSigs effectSigs (second :: first :: context) result} {env : Env context}
    {value : result.denote}
    (returns : Returns host pure program depth modes live (.letPair pair body) env value) :
    Returns host pure program depth (letPairModes pair modes) (shift 2 live) body
      (letPairEnv pair env) value := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact letPairReturn run

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

/-- The facts about a call's parts from which every run and every prefix of it uses at most
`budget` and has enough frames: for the first function, a frame at the call's depth and a bound on
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

/-- What a run that returns a value implies: a read returns at most its capacity's bytes. -/
def ReadReturns (pure : PureContext pureSigs) {context : List Ty} {result : ResultTy}
    (command : Command pureSigs effectSigs context result)
    (env : Env context) (outcome : Outcome result.denote) : Prop :=
  match command, outcome with
  | .read capacity, .returned value => value.2.data.size ≤ (capacity.denote pure.funs env).toNat
  | .readAll limit, .returned value =>
      value.2.data.size ≤ (limit.denote pure.funs env).toNat + 4096
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
  | readAll _ _ _ _ limit env execution =>
    change Exec host (Action.bind (readAll (limit.denote pure.funs env)) fun result =>
      .pure (result.errno, result.bytes)) _ _ _ _ at execution
    obtain ⟨_, _, middle, _, first, next, _⟩ := Exec.bind_iff.mp execution
    cases middle with
    | returned result =>
      cases next
      exact readAll_size first
    | exited _ =>
      obtain ⟨_, rfl, _⟩ := next
      trivial
    | trapped _ =>
      obtain ⟨_, rfl, _⟩ := next
      trivial
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

/-- `readAll` returns at most its limit's bytes and 4,096 more. -/
theorem Returns.readAll_size {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {limit : Expr pureSigs context .word} {env : Env context}
    {value : (Ty.pair .word .bytes).denote}
    (returns : Returns host pure program depth modes live (.readAll limit) env value) :
    value.2.data.size ≤ (limit.denote pure.funs env).toNat + 4096 := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact exec_readReturns run

/-! ## The parts of a command that returns -/

/-- A run of `pure result` that returns `value` returns `result`. -/
theorem exec_pure_value {World α : Type} {host : Host World} {result value : α}
    {world final : World} {trace : List Event}
    (run : Exec host (.pure result) world trace (.returned value) final) : value = result := by
  cases run
  rfl

/-- What a run of a command with the outcome `outcome` gives about its parts: a `ret` returns the
value of its expression, a `sys` command ends as a run of its action, a `bind` that returns has a
first command that returns and a second command that returns the same value, an `ite` that returns
has a branch that returns the same value, and a call ends as a run of the call. -/
def ReturnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    (host : Host World) (pure : PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) :
    {context : List Ty} → {result : ResultTy} → Command pureSigs effectSigs context result →
      Env context → Outcome result.denote → Prop
  | _, _, .ret value, env, .returned returned => returned = value.denote pure.funs env
  | _, _, .sys operation form args inputs buffers, env, outcome => ∃ world trace final,
      Exec host (form.runWith operation (args.map env.get) (inputs.map env.get)
        (buffers.map env.get)) world trace outcome final
  | _, _, .bind (intermediate := intermediate) first next, env, outcome => ∀ returned,
      outcome = .returned returned → ∃ value,
        Returns host pure program depth modes (bindLive intermediate next live) first env value ∧
          Returns host pure program depth (bindModes intermediate modes)
            (shift intermediate.bindCount live) next (intermediate.bindEnv value env) returned
  | _, _, .ite _ yes no, env, outcome => ∀ returned, outcome = .returned returned →
      Returns host pure program depth modes live yes env returned ∨
        Returns host pure program depth modes live no env returned
  | _, _, .call callee args, env, outcome => ∃ world trace final spent fits,
      ResourceCall host pure program callee (depth + 1)
        (Env.ofFn fun i => (args i).denote pure.funs env) world trace outcome final spent fits
  | _, _, _, _, _ => True

/-- Every run of a command gives `ReturnFact` of its outcome. -/
theorem returnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {context : List Ty}
    {result : ResultTy} {command : Command pureSigs effectSigs context result} {env : Env context}
    {world final : World} {trace : List Event} {outcome : Outcome result.denote} {spent : Nat}
    {fits : Bool}
    (run : ResourceExec host pure program depth modes live command env world trace outcome final
      spent fits) :
    ReturnFact host pure program depth modes live command env outcome := by
  cases run with
  | ret => rfl
  | sys execution => exact ⟨_, _, _, execution⟩
  | bind_return firstRun nextRun =>
    intro _ same
    subst same
    exact ⟨_, ⟨_, _, _, _, _, firstRun⟩, ⟨_, _, _, _, _, nextRun⟩⟩
  | bind_exit => exact fun _ same => by cases same
  | bind_trap => exact fun _ same => by cases same
  | ite_yes _ execution =>
    intro _ same
    subst same
    exact .inl ⟨_, _, _, _, _, execution⟩
  | ite_no _ execution =>
    intro _ same
    subst same
    exact .inr ⟨_, _, _, _, _, execution⟩
  | call execution => exact ⟨_, _, _, _, _, execution⟩
  | _ => trivial

/-- A command that returns `value` gives `ReturnFact` of that value. -/
theorem returns_fact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {context : List Ty}
    {result : ResultTy} {command : Command pureSigs effectSigs context result} {env : Env context}
    {value : result.denote}
    (returns : Returns host pure program depth modes live command env value) :
    ReturnFact host pure program depth modes live command env (.returned value) := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact returnFact run

/-! ## Charges of tests and calls -/

theorem ite_same {c : Prop} (decision : Decidable c) (a : Nat) : @ite Nat c decision a a = a := by
  cases decision <;> rfl

open Lean Meta Simp in
/-- Reads `if c then a else a` as `a` for any decision procedure of `c`.  `ite_self` does not apply
where a rewrite of the condition by `simp` kept the procedure of the condition before it, whose
type matches `Decidable c` only at the default transparency. -/
simproc_decl iteSame (@ite Nat _ _ _ _) := fun e => do
  let (``ite, #[_, c, decision, a, b]) := e.getAppFnArgs | return .continue
  unless a == b do return .continue
  return .done { expr := a, proof? := some (mkApp3 (mkConst ``ite_same) c decision a) }

/-- The reflector writes the test `C` of an `if` as `if C then true else !true`, and when that
value is false, `C` is false, for any decision procedure of `C = true`. -/
theorem reflected_test_false {C : Bool} {decision : Decidable (C = true)}
    (h : @ite Bool (C = true) decision true (!true) = false) : C = false := by
  cases decision with
  | isTrue holds =>
    have contradiction : true = false := h
    exact absurd contradiction (by decide)
  | isFalse fails => simpa using fails

/-- A charge `cost` followed by an `if` whose branches each charge `branch` is bounded by a bound
on `cost + branch`, for any decision procedure of the condition. -/
theorem ite_cost {c : Prop} {decision : Decidable c} {cost branch total : Nat}
    (bound : cost + branch ≤ total) : cost + @ite Nat c decision branch branch ≤ total := by
  cases decision <;> exact bound

theorem allocationCost_zero : Bytes.allocationCost 0 = 0 := rfl

/-- The call of `fd_filestat_get` charges 120 bytes for the block of its record, 71 bytes. -/
theorem filestat_block (trace : List Event) :
    sysCost (.record 8) Call.fdFilestatGet trace = 120 := by
  simp only [sysCost]
  decide

/-- A descriptor that `fd_filestat_get` does not reject lies below `2^32`. -/
theorem filestat_fd {fd : UInt64} (fits : Call.fdFilestatGet.reject [.word fd] = 0) :
    fd.toNat < 2 ^ 32 := by
  by_contra large
  have h : ¬ fd.toNat < 4294967296 := large
  simp [Call.reject, rejectArgs, Call.fdFilestatGet, Param.takesArg, Param.reject, Arg.value, h]
    at fits

/-- The block of the words that hold the last bytes of a SHA-256 message, `x &&& 63` of them, as
`finish` packs them eight to a word, charges at most 120 bytes. -/
theorem finish_block_le (x : UInt64) : blockCost (((x &&& 63) + 7) >>> 3).toNat ≤ 120 := by
  have hx : (x &&& 63).toNat ≤ 63 := by
    rw [UInt64.toNat_and]
    exact Nat.and_le_right
  have hs : ((x &&& 63) + 7).toNat = (x &&& 63).toNat + 7 := by
    rw [UInt64.toNat_add]
    simp only [UInt64.reduceToNat]
    omega
  rw [blockCost_eq, UInt64.toNat_shiftRight, hs]
  simp only [UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
  omega

/-! ## Loops with a bounded charge for each pass -/

section Loop

variable {World : Type} {host : Host World} {pureSigs : List Sig} {effectSigs : List EffectSig}
  {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
  {modes : List Mode} {live : Nat → Bool} {context : List Ty} {type : Ty}
  {test : Expr pureSigs (type :: .word :: context) .bool}
  {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
  {env : Env context}

/-- A loop whose test charges at most `t` and whose step is bounded by `s` from every state of
the invariant `held`, which every returned step keeps, charges at most `t + s` for each pass and
`t` for the last test. -/
theorem loop_bounded (held : type.denote → Prop) {t s : Nat}
    (testCost : ∀ index state, held state →
      pure.loopTestCost depth modes live test step env index state ≤ t)
    (testFits : ∀ index state, held state → pure.loopTestFits depth test env index state = true)
    (stepBounded : ∀ index state, held state →
      Bounded host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) s)
    (kept : ∀ index state next, held state →
      Returns host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) next → held next) :
    ∀ remaining index state, held state →
      LoopBounded host pure program depth modes live test step env remaining index state
        (remaining * (t + s) + t) := by
  intro remaining
  induction remaining with
  | zero =>
    intro index state _
    refine ⟨fun _ _ _ _ _ _ run => ?_, fun _ _ _ _ _ _ progress => ?_⟩
    · cases run
      exact ⟨Nat.zero_le _, rfl⟩
    · cases progress with
      | refl => exact ⟨Nat.zero_le _, rfl⟩
      | returned execution =>
        cases execution
        exact ⟨Nat.zero_le _, rfl⟩
  | succ remaining ih =>
    intro index state current
    have more : (remaining + 1) * (t + s) + t = remaining * (t + s) + t + (t + s) := by
      rw [Nat.succ_mul]
      omega
    have cost := testCost index state current
    have valid := testFits index state current
    have exec : ∀ world trace outcome final spent fits,
        ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index
          state world trace outcome final spent fits →
        spent ≤ (remaining + 1) * (t + s) + t ∧ fits = true := by
      intro _ _ _ _ _ _ run
      rw [more]
      cases run with
      | stop chosen => exact ⟨by omega, valid⟩
      | next chosen stepRun restRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        obtain ⟨restCost, restFits⟩ := (ih (index + 1) _
          (kept index state _ current ⟨_, _, _, _, _, stepRun⟩)).1 _ _ _ _ _ _ restRun
        rw [valid, stepFits, restFits]
        exact ⟨by omega, rfl⟩
      | exit chosen stepRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        rw [valid, stepFits]
        exact ⟨by omega, rfl⟩
      | trap chosen stepRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        rw [valid, stepFits]
        exact ⟨by omega, rfl⟩
    refine ⟨exec, fun _ _ _ _ _ _ progress => ?_⟩
    cases progress with
    | refl => exact ⟨Nat.zero_le _, rfl⟩
    | test_charge => exact ⟨by rw [more]; omega, valid⟩
    | returned execution => exact exec _ _ _ _ _ _ execution
    | step chosen progress =>
      obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).2 _ _ _ _ _ _ progress
      rw [valid, stepFits, more]
      exact ⟨by omega, rfl⟩
    | next chosen stepRun progress =>
      obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := (ih (index + 1) _
        (kept index state _ current ⟨_, _, _, _, _, stepRun⟩)).2 _ _ _ _ _ _ progress
      rw [valid, stepFits, restFits, more]
      exact ⟨by omega, rfl⟩

theorem LoopBounded.mono {remaining index : Nat} {state : type.denote} {budget larger : Nat}
    (bounded : LoopBounded host pure program depth modes live test step env remaining index state
      budget) (le : budget ≤ larger) :
    LoopBounded host pure program depth modes live test step env remaining index state larger :=
  ⟨fun _ _ _ _ _ _ run => by
      obtain ⟨cost, valid⟩ := bounded.1 _ _ _ _ _ _ run
      exact ⟨by omega, valid⟩,
    fun _ _ _ _ _ _ progress => by
      obtain ⟨cost, valid⟩ := bounded.2 _ _ _ _ _ _ progress
      exact ⟨by omega, valid⟩⟩

/-- The sum of `charge` over `remaining` indices from `index`. -/
def passSum (charge : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | index, remaining + 1 => charge index + passSum charge (index + 1) remaining

/-- The sum of `charge` over the indices of the elements of `ls` from `index` is at most the sum
of `g` over the elements when `charge` at each index is at most `g` of its element. -/
theorem passSum_le {α : Type} (charge : Nat → Nat) (g : α → Nat) :
    ∀ (ls : List α) (index : Nat), (∀ j (hj : j < ls.length), charge (index + j) ≤ g ls[j]) →
      passSum charge index ls.length ≤ (ls.map g).sum
  | [], _, _ => by simp [passSum]
  | l :: ls, index, h => by
    have h0 := h 0 (by simp)
    have ih := passSum_le charge g ls (index + 1) fun j hj => by
      have := h (j + 1) (by simp; omega)
      rwa [show index + (j + 1) = index + 1 + j by omega, List.getElem_cons_succ] at this
    simp only [List.length_cons, passSum, List.map_cons, List.sum_cons]
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    omega

theorem sum_map_four {α : Type} (f : α → Nat) :
    ∀ ls : List α, (ls.map fun l => 4 * f l).sum = 4 * (ls.map f).sum
  | [] => rfl
  | l :: ls => by
    simp only [List.map_cons, List.sum_cons, sum_map_four f ls]
    omega

/-- A loop whose test charges at most `t` and whose step at pass `index` is bounded by
`charge index` from every state of the invariant `held`, which every returned step keeps, charges
at most the sum of `charge` over its passes and `t` for each test. -/
theorem loop_bounded_sum (held : type.denote → Prop) {t : Nat} (charge : Nat → Nat)
    (testCost : ∀ index state, held state →
      pure.loopTestCost depth modes live test step env index state ≤ t)
    (testFits : ∀ index state, held state → pure.loopTestFits depth test env index state = true)
    (stepBounded : ∀ index state, held state →
      Bounded host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) (charge index))
    (kept : ∀ index state next, held state →
      Returns host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) next → held next) :
    ∀ remaining index state, held state →
      LoopBounded host pure program depth modes live test step env remaining index state
        (passSum charge index remaining + (remaining + 1) * t) := by
  intro remaining
  induction remaining with
  | zero =>
    intro index state _
    refine ⟨fun _ _ _ _ _ _ run => ?_, fun _ _ _ _ _ _ progress => ?_⟩
    · cases run
      exact ⟨Nat.zero_le _, rfl⟩
    · cases progress with
      | refl => exact ⟨Nat.zero_le _, rfl⟩
      | returned execution =>
        cases execution
        exact ⟨Nat.zero_le _, rfl⟩
  | succ remaining ih =>
    intro index state current
    have more : passSum charge index (remaining + 1) + (remaining + 1 + 1) * t =
        passSum charge (index + 1) remaining + (remaining + 1) * t + (t + charge index) := by
      simp only [passSum]
      rw [Nat.succ_mul]
      omega
    have cost := testCost index state current
    have valid := testFits index state current
    have exec : ∀ world trace outcome final spent fits,
        ResourceLoopExec host pure program depth modes live test step env (remaining + 1) index
          state world trace outcome final spent fits →
        spent ≤ passSum charge index (remaining + 1) + (remaining + 1 + 1) * t ∧ fits = true := by
      intro _ _ _ _ _ _ run
      rw [more]
      cases run with
      | stop chosen => exact ⟨by omega, valid⟩
      | next chosen stepRun restRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        obtain ⟨restCost, restFits⟩ := (ih (index + 1) _
          (kept index state _ current ⟨_, _, _, _, _, stepRun⟩)).1 _ _ _ _ _ _ restRun
        rw [valid, stepFits, restFits]
        exact ⟨by omega, rfl⟩
      | exit chosen stepRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        rw [valid, stepFits]
        exact ⟨by omega, rfl⟩
      | trap chosen stepRun =>
        obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
        rw [valid, stepFits]
        exact ⟨by omega, rfl⟩
    refine ⟨exec, fun _ _ _ _ _ _ progress => ?_⟩
    cases progress with
    | refl => exact ⟨Nat.zero_le _, rfl⟩
    | test_charge => exact ⟨by rw [more]; omega, valid⟩
    | returned execution => exact exec _ _ _ _ _ _ execution
    | step chosen progress =>
      obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).2 _ _ _ _ _ _ progress
      rw [valid, stepFits, more]
      exact ⟨by omega, rfl⟩
    | next chosen stepRun progress =>
      obtain ⟨stepCost, stepFits⟩ := (stepBounded index state current).1 _ _ _ _ _ _ stepRun
      obtain ⟨restCost, restFits⟩ := (ih (index + 1) _
        (kept index state _ current ⟨_, _, _, _, _, stepRun⟩)).2 _ _ _ _ _ _ progress
      rw [valid, stepFits, restFits, more]
      exact ⟨by omega, rfl⟩

end Loop

end Verified.Wasi.Resource
