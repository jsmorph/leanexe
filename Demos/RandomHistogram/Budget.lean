import Demos.RandomHistogram.CommandStart
import Demos.RandomHistogram.Compiled
import Verified.Examples.WasiSysTotal

/-! The resource model's charge of the random-residue histogram's `main`.  -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

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

/-- Every state that a run of the loop returns from a state of the invariant `held`, which every
returned step keeps, is of the invariant. -/
theorem loop_kept (held : type.denote → Prop)
    (kept : ∀ index state next, held state →
      Returns host pure program depth (loopModes .owned modes) (shift 2 (loopLive test step live))
        step (loopEnv env index state) next → held next) :
    ∀ remaining index state {world trace value final spent fits}, held state →
      ResourceLoopExec host pure program depth modes live test step env remaining index state
        world trace (.returned value) final spent fits → held value := by
  intro remaining
  induction remaining with
  | zero =>
    intro index state _ _ _ _ _ _ current run
    cases run
    exact current
  | succ remaining ih =>
    intro index state _ _ _ _ _ _ current run
    cases run with
    | stop => exact current
    | next chosen stepRun restRun =>
      exact ih (index + 1) _ (kept index state _ current ⟨_, _, _, _, _, stepRun⟩) restRun

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

/-! ## The budget -/

/-- The bytes of the arguments, with the four-byte pointer of each and three bytes of alignment,
for which the budget holds: 6 MiB, the most that Linux lets the strings and pointers of `argv` and
`envp` take together. -/
def argsLimit : Nat := 6291456

/-- The largest N for which the budget fits the native executable's memory. -/
def drawLimit : Nat := 12839935

/-- The charge of one pass of the loop: two copies of the counts' block of 136 bytes for the
expressions before the call, the block of the call's buffer of at most 4,096 bytes, 4,144 bytes,
and a copy of that buffer and of the counts for the test of the call's errno. -/
def passCharge : Nat := 8696

/-- A bound on the charge of `main`: the block of `args` and seven copies of the argument bytes,
the loop's initial counts and two copies of the final counts, 136 bytes each, the charge of
`render`, at most 17,136 bytes, and a pass for each of the at most `drawLimit / 512 + 1` passes. -/
def budget : Nat := 8 * Bytes.allocationCost argsLimit + 17544 + (drawLimit / 512 + 1) * passCharge

theorem budget_fits : 4096 + budget ≤ 65536 * 4096 := by decide

/-- One more pass does not fit, so `drawLimit` is the largest N for which the budget fits. -/
theorem budget_full : 65536 * 4096 < 4096 + budget + passCharge := by decide

/-! ## Facts about the reflected program -/

open Lean Meta in
/-- The value at `index` of an environment given as a chain of `Env.cons`. -/
private partial def envValueAt (env : Lean.Expr) (index : Nat) : MetaM (Option Lean.Expr) := do
  match (← whnfD env).getAppFnArgs with
  | (``Env.cons, #[_, _, value, rest]) =>
    if index == 0 then return some value else envValueAt rest (index - 1)
  | _ => return none

open Lean Meta Simp in
/-- Reads `Env.get env (Var.ofIndex Γ i h)` as the `i`-th value of `env` when `env` is a chain of
`Env.cons`, a definitional step. -/
dsimproc_decl envGet (Env.get _ (Var.ofIndex _ _ _)) := fun e => do
  let (``Env.get, #[_, _, env, reference]) := e.getAppFnArgs | return .continue
  let (``Var.ofIndex, #[_, _, index, _]) := reference.getAppFnArgs | return .continue
  let some index := index.rawNatLit? <|> index.nat? | return .continue
  let some value ← envValueAt env index | return .continue
  return .done value

private theorem ite_cost {c : Prop} {decision : Decidable c} {cost branch total : Nat}
    (bound : cost + branch ≤ total) : cost + @ite Nat c decision branch branch ≤ total := by
  cases decision <;> exact bound

/-- `parseN` allocates nothing. -/
theorem parseN_charge (env : Env [Ty.bytes]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there.there.there.there env = 0 := by
  cases env with
  | cons bytes rest =>
    cases rest
    exact (command.pureSources.parseN.bound_eq bytes).trans rfl

/-- `tally` allocates nothing. -/
theorem tally_charge (env : Env [Ty.array Elem.word, Ty.bytes]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there env = 0 := by
  cases env with
  | cons counts rest =>
    cases rest with
    | cons bytes rest =>
      cases rest
      exact (command.pureSources.tally.bound_eq counts bytes).trans rfl

/-- The type of the state of `main`'s loop: the counts, the words still to draw, and the errno of
a failed call. -/
abbrev stateTy : Ty := (Ty.array Elem.word).pair (Ty.elem (Elem.word.prod Elem.word))

/-- The command's `appendLine` charges what the pure core's does. -/
theorem appendLine_cost_eq (text : Array UInt64) (c : UInt64) :
    command.pureSources.appendLine.cost (⟨text⟩, c) = compiled.appendLine.cost (⟨text⟩, c) := by
  rw [command.pureSources.appendLine.cost_eq, compiled.appendLine.cost_eq]

private theorem exec_pure_value {World α : Type} {host : Host World} {result value : α}
    {world final : World} {trace : List Event}
    (run : Exec host (.pure result) world trace (.returned value) final) : value = result :=
  Outcome.returned.inj (exec_pure_shape run).2.1

/-- The charge of a call of `render`. -/
theorem render_charge (counts : Array UInt64) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get FVar.here
      (Env.cons counts Env.nil) = command.pureSources.render.bound counts :=
  rfl

/-- The command's `render` charges at most 17,136 bytes, as the pure core's does. -/
theorem render_bound_command (counts : Array UInt64) :
    command.pureSources.render.bound counts ≤ 17136 := by
  refine le_of_eq_of_le (command.pureSources.render.bound_eq counts) ?_
  refine le_of_eq_of_le ?_ (render_bound counts)
  rw [compiled.render.bound_eq]
  simp only [appendLine_cost_eq]

/-- `random_get` of `8 · min r 512` bytes charges at most the block of 4,096 bytes. -/
theorem random_charge (r : UInt64) (trace : List Event) :
    sysCostWith (.flat 0 true) Call.randomGet [8 * min r 512] [] trace ≤ 4144 := by
  have eight := toNat_eight_min r
  simp only [sysCostWith, flatCapacityWith, Call.randomGet, List.headD_cons, readCost]
  split
  · exact (allocationCost_mono (show (8 * min r 512).toNat ≤ 4096 by omega)).trans (by decide)
  · exact Nat.zero_le _

/-- A returned result of `random_get` of `8 · min r 512` bytes holds at most 4,096 bytes. -/
theorem random_bytes_le {World : Type} {host : Host World} {r : UInt64} {world final : World}
    {trace : List Event} {value : UInt64 × LeanExe.Bytes}
    (run : Exec host ((SysForm.flat 0 true).runWith Call.randomGet [8 * min r 512] []) world
      trace (.returned value) final) :
    value.2.data.size ≤ 4096 := by
  obtain ⟨errno, committed, after, rest, -, permitted, next⟩ :=
    exec_sys_returned run (randomGet_accepted r)
  rw [exec_pure_value next]
  have shape : committed.map (·.data.size) = [(8 * min r 512).toNat] :=
    (host.sys_bound permitted).1
  rw [toNat_eight_min] at shape
  change ((sysReply errno committed).bytes 0).data.size ≤ 4096
  rcases committed with _ | ⟨buffer, _ | ⟨_, _⟩⟩ <;> simp at shape
  have small : buffer.data.size ≤ 4096 := by
    rw [shape]
    omega
  by_cases zero : errno = 0
  · subst zero
    simpa [sysReply, Reply.bytes] using small
  · have empty : (sysReply errno [buffer]).outputs = [] := ite_eq_right zero
    simp only [Reply.bytes, empty, List.getElem?_nil, Option.getD_none]
    exact Nat.zero_le _

/-- The reflected `parseN` is `parseN`. -/
theorem parseN_reflected (bytes : Bytes) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get
      FVar.here.there.there.there.there.there.there.there (Env.cons bytes Env.nil) =
      parseN bytes := by
  rw [← command.pureSources.parseN.denote_eq]
  rfl

/-- The reflected `tally` is `tally`. -/
theorem tally_reflected (counts : Array UInt64) (bytes : Bytes) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get
      FVar.here.there.there.there.there (Env.cons counts (Env.cons bytes Env.nil)) =
      tally counts bytes := by
  rw [← command.pureSources.tally.denote_eq]
  rfl

theorem tally_size (counts : Array UInt64) (bytes : Bytes) :
    (tally counts bytes).size = counts.size :=
  LeanExe.Dialect.loop_induction (n := bytes.size / 8) (init := counts)
    (f := fun j c => countWord c (wordAt bytes (8 * j))) (fun _ c => c.size = counts.size) rfl
    (fun _ c _ held => by simp [countWord, held])

/-! ## The values that the charges read -/

/-- A returned `args` result with errno 0 holds the bytes that a successful `args_get` reply
gave. -/
theorem args_got {World : Type} {host : Host World} {values : List UInt64}
    {world final : World} {trace : List Event}
    {value : UInt64 × UInt64 × UInt64 × LeanExe.Bytes}
    (run : Exec host (SysForm.reported.run Call.argsGet values) world trace (.returned value)
      final)
    (zero : value.1 = 0) :
    ∃ world got after, host.sys world Call.argsGet [] (.returned 0 got) after ∧
      value.2.2.2 = (sysReply 0 got).bytes 0 := by
  obtain ⟨errno, sizes, middle, rest, -, -, next⟩ := exec_sys_returned run rfl
  split at next
  · rename_i nonzero
    rw [exec_pure_value next] at zero
    simp [SysForm.value, wordsBytesValue] at zero
    simp [zero] at nonzero
  split at next
  · rw [exec_pure_value next] at zero
    simp [SysForm.value, wordsBytesValue] at zero
  obtain ⟨gotErrno, got, after, _, -, getter, next⟩ := exec_sys_returned next rfl
  split at next
  · rename_i nonzero
    rw [exec_pure_value next] at zero
    simp [SysForm.value, wordsBytesValue] at zero
    simp [zero] at nonzero
  rename_i gotZero
  have zeroErrno : gotErrno = 0 := by simpa [sysReply] using gotZero
  subst zeroErrno
  rw [exec_pure_value next]
  exact ⟨_, _, _, getter, rfl⟩

/-- What a run of a command with the outcome `outcome` gives about its parts: a `ret` returns the
value of its expression, a `sys` command ends as a run of its action, a `bind` that returns has a
first command that returns and a second command that returns the same value, an `ite` that
returns has a branch that returns the same value, and a loop that returns has a run of its passes
that returns the same value. -/
def ReturnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    (host : Host World) (pure : PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (modes : List Mode) (live : Nat → Bool) :
    {context : List Ty} → {result : ResultTy} → Command pureSigs effectSigs context result →
      Env context → Outcome result.denote → Prop
  | _, _, .ret value, env, .returned returned => returned = value.denote pure.funs env
  | _, _, .sys operation form args inputs, env, outcome => ∃ world trace final,
      Exec host (form.runWith operation (args.map env.get) (inputs.map env.get)) world trace
        outcome final
  | _, _, .bind (intermediate := intermediate) first next, env, outcome => ∀ returned,
      outcome = .returned returned → ∃ value,
        Returns host pure program depth modes (bindLive intermediate next live) first env value ∧
          Returns host pure program depth (bindModes intermediate modes)
            (shift intermediate.bindCount live) next (intermediate.bindEnv value env) returned
  | _, _, .ite _ yes no, env, outcome => ∀ returned, outcome = .returned returned →
      Returns host pure program depth modes live yes env returned ∨
        Returns host pure program depth modes live no env returned
  | _, _, .loop count initial test step, env, outcome => ∀ returned,
      outcome = .returned returned → ∃ world trace final spent fits,
        ResourceLoopExec host pure program depth modes live test step env
          (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env) world trace
          (.returned returned) final spent fits
  | _, _, _, _, _ => True

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
  | loop execution =>
    intro _ same
    subst same
    exact ⟨_, _, _, _, _, execution⟩
  | _ => trivial

theorem returns_fact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {context : List Ty}
    {result : ResultTy} {command : Command pureSigs effectSigs context result} {env : Env context}
    {value : result.denote}
    (returns : Returns host pure program depth modes live command env value) :
    ReturnFact host pure program depth modes live command env (.returned value) := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact returnFact run

/-! ## The budget of `main` -/

/-- Proves a bound on the charge of an expression: evaluates its liveness tests, reads its
variables, and leaves the copies to `omega`. -/
local macro "charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.loopTestCost, Expr.allocs, Var.cost, Var.ownedCost,
      Expr.ownedCost, Expr.mode, coerceCost, Ty.copyCost, envGet, Expr.denote, Args.get_cons_zero',
      Args.get_cons_zero, Env.ofFn, argsSum, callCredits, ResultTy.bindEnv, loopEnv, loopModes,
      parseN_charge, tally_charge, render_charge, allocCost, Elem.width, sumBelow,
      UInt64.reduceToNat, Nat.add_zero, Nat.zero_add, ↓reduceIte, ite_self] <;>
   omega))

/-- Proves that a step of the loop keeps the counts' size at 10. -/
local macro "kept_tac" : tactic => `(tactic|
  (intro index state next held returned
   obtain ⟨counts, left, errno⟩ := state
   have held' : counts.size = 10 := held
   obtain ⟨count, first, rest⟩ := returns_fact returned next rfl
   obtain ⟨random, inner, branch⟩ := returns_fact rest next rfl
   rcases returns_fact branch next rfl with yes | no
   · have value := returns_fact yes
     simp only [ReturnFact] at value
     rw [value]
     simpa [Expr.denote, envGet] using held'
   · have value := returns_fact no
     simp only [ReturnFact] at value
     rw [value]
     simp [Expr.denote, envGet, Env.ofFn, Args.get_cons_zero', Args.get_cons_zero, tally_reflected,
       tally_size, held']))

/-- Proves that the loop's initial counts have ten elements. -/
local macro "initial_tac" : tactic => `(tactic|
  (simp [Expr.denote, envGet, LeanExe.Dialect.build_size]))

/-- Proves the frames of an expression that calls no function that takes the call depth. -/
local macro "fits" : tactic => `(tactic| exact Expr.fits_of_depthCalls _ _ _ (by decide) _)

/-- Proves `Bounded` of a `ret`. -/
local macro "ret_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (by charge) (by fits)))

/-- Proves `Bounded` of a `write`, which charges nothing. -/
local macro "write_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule))

/-- Reduces `Bounded` of a `bind` to its parts with the budgets `first` and `next`. -/
local macro "bind_bound " first:term:max next:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $first $next (by omega) ?_ ?_))

/-- Reduces `Bounded` of an `ite` to its branches with the budget `branch` for each. -/
local macro "ite_bound " branch:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $branch $branch (ite_cost (by charge)) (by fits) (fun _ => ?_) (fun _ => ?_)))

/-- Every run and every prefix of `main`'s body charges at most `budget` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes and whose successful
`args_get` replies hold a buffer from which `parseN` reads at most `drawLimit`. -/
theorem body_bounded {World : Type} {host : Host World}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ argsLimit)
    (drawn : ∀ world got after, host.sys world Call.argsGet [] (.returned 0 got) after →
      (parseN ((sysReply 0 got).bytes 0)).toNat ≤ drawLimit) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs) .nil 0 []
      (fun _ => false) command.main.func.body .nil budget := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    bound (Nat.le_refl (Bytes.allocationCost argsLimit))
  unfold budget
  generalize hA : Bytes.allocationCost argsLimit = A at reported ⊢
  have room : (drawLimit / 512 + 1) * passCharge = 25078 * 8696 := by decide
  rw [room]
  bind_bound A (7 * A + 17544 + 25078 * 8696)
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments returned
  obtain ⟨_, _, _, execution⟩ := returns_fact returned
  change Exec _ (SysForm.reported.run Call.argsGet []) _ _ _ _ at execution
  have size : arguments.2.2.2.data.size ≤ argsLimit :=
    Verified.Examples.WasiSys.args_bytes_le (host := observedHost host) (values := [])
      (fun _ _ _ permitted => bound _ _ _ permitted.1) execution
  have parsed : arguments.1 = 0 → (parseN arguments.2.2.2).toNat ≤ drawLimit := fun zero => by
    obtain ⟨_, _, _, getter, same⟩ := args_got execution zero
    rw [same]
    exact drawn _ _ _ getter.1
  obtain ⟨errno, _, _, bytes⟩ := arguments
  have copy : Bytes.allocationCost bytes.data.size ≤ A := hA ▸ allocationCost_mono size
  apply bounded_of_rule
  intro _ _ rule
  refine rule (6 * A + 17544 + 25078 * 8696) (6 * A + 17544 + 25078 * 8696)
    (ite_cost (by charge)) (by fits) (fun _ => ?_) (fun chosen => ?_)
  · ret_bound
  have ok : errno = 0 := by simpa [Expr.denote, envGet, CmpOp.apply] using chosen
  have small : (parseN bytes).toNat ≤ drawLimit := parsed ok
  bind_bound A (5 * A + 17544 + 25078 * 8696)
  · ret_bound
  intro n returnedN
  have hn : n = parseN bytes := by
    have value := returns_fact returnedN
    simp only [ReturnFact, Expr.denote, envGet, Env.ofFn] at value
    rw [value, parseN_reflected]
    rfl
  subst hn
  ite_bound (4 * A + 17544 + 25078 * 8696)
  · ret_bound
  bind_bound (2 * A + 136 + 25078 * 8696) (2 * A + 17408)
  · apply bounded_of_rule
    intro _ _ rule
    refine rule (25078 * 8696) (by charge) ?_ ?_
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine LoopBounded.mono (loop_bounded (type := stateTy) (t := 0) (s := 8696)
      (fun (state : Array UInt64 × UInt64 × UInt64) => state.1.size = 10) ?_ ?_ ?_ ?_ _ _ _ ?_) ?_
    · intro index state _
      charge
    · intro index state _
      exact Expr.fits_of_depthCalls _ _ _ (by decide) _
    · intro index state held
      obtain ⟨counts, left, errno⟩ := state
      have held' : counts.size = 10 := held
      bind_bound 136 8560
      · ret_bound
      intro count returnedCount
      have hcount : count = min left 512 := by
        have value := returns_fact returnedCount
        simp only [ReturnFact] at value
        rw [value]
        simp only [Expr.denote, envGet, CmpOp.apply]
        show (if decide (left ≤ 512) = true then left else 512) = (if left ≤ 512 then left else 512)
        by_cases h : left ≤ 512 <;> simp [h]
      subst hcount
      bind_bound 4280 4280
      · bind_bound 136 4144
        · ret_bound
        intro capacity returnedCapacity
        have hcap : capacity = 8 * min left 512 := by
          have value := returns_fact returnedCapacity
          simp only [ReturnFact] at value
          rw [value]
          rfl
        subst hcap
        apply bounded_of_rule
        intro _ _ rule
        exact rule (fun _ trace _ _ _ => random_charge left trace)
          (fun _ trace _ _ _ => random_charge left trace)
      intro random returnedRandom
      have randomSize : random.2.data.size ≤ 4096 := by
        obtain ⟨capacity, first, next⟩ := returns_fact returnedRandom random rfl
        have hcap : capacity = 8 * min left 512 := by
          have value := returns_fact first
          simp only [ReturnFact] at value
          rw [value]
          rfl
        subst hcap
        obtain ⟨_, _, _, execution⟩ := returns_fact next
        exact random_bytes_le execution
      obtain ⟨randomErrno, randomBytes⟩ := random
      have randomCopy : Bytes.allocationCost randomBytes.data.size ≤ 4144 :=
        (allocationCost_mono randomSize).trans (by decide)
      ite_bound 0
      · ret_bound
      · ret_bound
    · kept_tac
    · initial_tac
    · show ((parseN bytes / 512 + 1).toNat * (0 + 8696) + 0 ≤ 25078 * 8696)
      have count : ((parseN bytes) / 512 + 1).toNat = (parseN bytes).toNat / 512 + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_div]
        simp only [UInt64.reduceToNat]
        have := (parseN bytes).toNat_lt
        omega
      rw [count]
      have : (parseN bytes).toNat / 512 + 1 ≤ 25078 := by
        unfold drawLimit at small
        omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _
  intro drawn returnedLoop
  have drawnSize : drawn.1.size = 10 := by
    obtain ⟨_, _, _, _, _, loopRun⟩ := returns_fact returnedLoop drawn rfl
    exact loop_kept (type := stateTy)
      (fun (state : Array UInt64 × UInt64 × UInt64) => state.1.size = 10) (by kept_tac) _ 0 _
      (by initial_tac) loopRun
  obtain ⟨counts, left, errno⟩ := drawn
  have drawnSize' : counts.size = 10 := drawnSize
  have renderBound := render_bound_command counts
  ite_bound (A + 17272)
  · ret_bound
  bind_bound (A + 17272) 0
  · bind_bound (A + 17272) 0
    · ret_bound
    · intro _ _
      write_bound
  · intro _ _
    ret_bound

end Demos.RandomHistogram
