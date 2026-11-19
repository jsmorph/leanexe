import Verified.Wasi.ResourcePrefix

/-! Compositional bounds on the resource semantics of effect commands.  `Bounded` states that every
run and every prefix of a command uses at most a budget and has enough frames, and `Rule` gives,
for each form of command, the facts about its parts from which that follows.  A bound on an effect
function's body follows by `bounded_of_rule` at each command.  `loop_bounded` bounds a loop whose
passes each charge at most a constant from the states of an invariant that every pass keeps. -/

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
  | .read buffer start count =>
      pure.sysTakeCost depth modes live [start, count] [] [buffer] env ≤ budget → conclusion
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
  | read => exact fun cost => ⟨cost, rfl⟩
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
  | read_charge => exact fun cost => ⟨cost, rfl⟩
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

/-- What a run of a `ret` that returns a value gives: the value of its expression. -/
private def RetValue (pure : PureContext pureSigs) : {context : List Ty} → {result : ResultTy} →
    Command pureSigs effectSigs context result → Env context → Outcome result.denote → Prop
  | _, _, .ret value, env, .returned returned => returned = value.denote pure.funs env
  | _, _, _, _, _ => True

private theorem retValue {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {context : List Ty} {result : ResultTy}
    {command : Command pureSigs effectSigs context result} {env : Env context}
    {world trace outcome final spent fits}
    (run : ResourceExec host pure program depth modes live command env world trace outcome final
      spent fits) :
    RetValue pure command env outcome := by
  cases run with
  | ret => rfl
  | _ => trivial

/-- A run of a `bind` whose first command is a `ret` that returns a value is a run of the next
command that returns it, from the environment with the value of the `ret`.  The reflector binds
each argument of an effect command that is not a variable this way, so a read's result reaches
`Returns.read_size` through one application for each such argument. -/
theorem Returns.bind_ret {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {context : List Ty} {type : Ty} {result : ResultTy}
    {value : Expr pureSigs context type}
    {next : Command pureSigs effectSigs (type :: context) result} {env : Env context}
    {returned : result.denote}
    (returns : Returns host pure program depth modes live (.bind (.ret value) next) env returned) :
    Returns host pure program depth (.owned :: modes) (shift 1 live) next
      (.cons (value.denote pure.funs env) env) returned := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  cases run with
  | bind_return first rest =>
    have same := retValue first
    dsimp only [RetValue] at same
    rw [same] at rest
    exact ⟨_, _, _, _, _, rest⟩

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

/-- What a run that returns a value implies: a read places at most the buffer's size and keeps the
buffer's size, and `readAll` returns at most its limit's bytes and 4,096 more. -/
def ReadReturns (pure : PureContext pureSigs) {context : List Ty} {result : ResultTy}
    (command : Command pureSigs effectSigs context result)
    (env : Env context) (outcome : Outcome result.denote) : Prop :=
  match command, outcome with
  | .read buffer _ _, .returned value =>
      value.2.1.toNat ≤ (env.get buffer).data.size ∧
        value.2.2.data.size = (env.get buffer).data.size
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
  | read _ _ _ _ buffer start count env execution =>
    change Exec host (Action.bind (readStdin (env.get buffer) (env.get start) (env.get count))
      fun result => .pure (fillValue result)) _ _ _ _ at execution
    obtain ⟨_, _, middle, _, first, next, _⟩ := Exec.bind_iff.mp execution
    cases middle with
    | returned result =>
      cases next
      exact readStdin_returns first
    | exited _ =>
      obtain ⟨_, rfl, _⟩ := next
      trivial
    | trapped _ =>
      obtain ⟨_, rfl, _⟩ := next
      trivial
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

/-- A read places at most the buffer's size and keeps the buffer's size. -/
theorem Returns.read_size {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {buffer : Var context .bytes} {start count : Var context .word}
    {env : Env context} {value : (wordsBytesTy 2).denote}
    (returns : Returns host pure program depth modes live (.read buffer start count) env value) :
    value.2.1.toNat ≤ (env.get buffer).data.size ∧
      value.2.2.data.size = (env.get buffer).data.size := by
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

end Loop

end Verified.Wasi.Resource
