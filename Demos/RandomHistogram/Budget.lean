import Demos.RandomHistogram.CommandStart
import Demos.RandomHistogram.Compiled
import Verified.Examples.WasiSysTotal

/-! The resource model's charge of the random-residue histogram's `main`, the budget that the
generated `command.start` without guest traps and `command.total` take as a bound on every prefix
of `main`.

`body_bounded` bounds every run and every prefix of `main`'s body by `budget` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes, for every N.  The model
charges a copy of an owned value at each use after which the value stays live, and it credits no
release.  The reflector splits the result of `args`, the loop's state, and the result of
`randomGet` into their components where `main` binds them, so no use copies them.  A pass of the
draw loop charges nothing: `random_get` fills the buffer that the loop's state carries, the call
takes the buffer's variable, which dies at the call, without a copy, and `tally` reads the buffer
and updates the counts in place.  The charge of `main` holds the block of `args`, the loop's
initial counts and buffer, and the charge of `render`.  `writeAll` charges nothing
(`writeAll_bounded`): it computes the window of the output in words, and each of its passes writes
a window of the output, which it borrows, in place.  `loop_bounded` of
`Verified/Wasi/ResourceRules.lean` bounds the draw loop and the loop of `writeAll`.

`budget_fits` states that the budget fits the 4,096 pages of the native executable above the
heap's start at byte 4,096.  Linux 4.13 and later limit the strings and pointers of `argv` and
`envp` together to at most 6 MiB, `argsLimit` (`get_arg_page` of `fs/exec.c` in v4.13,
`bprm_stack_limits` in v6.12). -/

namespace Demos.RandomHistogram

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

/-! ## The budget -/

/-- The bytes of the arguments, with the four-byte pointer of each and three bytes of alignment,
for which the budget holds: 6 MiB, the most that Linux lets the strings and pointers of `argv` and
`envp` take together. -/
def argsLimit : Nat := 6291456

/-- A bound on the charge of `main`: the block of `args`, the loop's initial counts of 136 bytes
and buffer of 4,144 bytes, and the charge of `render`, at most 17,136 bytes. -/
def budget : Nat := Bytes.allocationCost argsLimit + 21416

theorem budget_fits : 4096 + budget ≤ 65536 * 4096 := by decide

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
theorem tally_charge (env : Env [Ty.array Elem.word, Ty.bytes, Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there env = 0 := by
  cases env with
  | cons counts rest =>
    cases rest with
    | cons bytes rest =>
      cases rest with
      | cons count rest =>
        cases rest
        exact (command.pureSources.tally.bound_eq counts bytes count).trans rfl

/-- The type of the state of `main`'s loop: the counts, the buffer, the words still to draw, and
the errno of a failed call. -/
abbrev stateTy : Ty :=
  (Ty.array Elem.word).pair (Ty.bytes.pair (Ty.elem (Elem.word.prod Elem.word)))

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

/-- The reflected `parseN` is `parseN`. -/
theorem parseN_reflected (bytes : Bytes) :
    (PureContext.ofProg command.pure.program command.pure.funs).funs.get
      FVar.here.there.there.there.there.there.there.there (Env.cons bytes Env.nil) =
      parseN bytes := by
  rw [← command.pureSources.parseN.denote_eq]
  rfl

/-! ## The values that the charges read -/

/-- A returned `args` result with errno 0 holds the bytes that a successful `args_get` reply
gave. -/
theorem args_got {World : Type} {host : Host World} {values : List UInt64}
    {world final : World} {trace : List Event}
    {value : UInt64 × UInt64 × UInt64 × LeanExe.Bytes}
    (run : Exec host (SysForm.reported.runWith Call.argsGet values [] []) world trace
      (.returned value) final)
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
value of its expression, a `sys` command, a `write`, and an `exit` end as runs of their actions, a
`bind` that returns has a first command that returns and a second command that returns the same
value, an `ite` that returns has a branch that returns the same value, and a loop that returns has
a run of its passes that returns the same value. -/
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
  | _, _, .loop count initial test step, env, outcome => ∀ returned,
      outcome = .returned returned → ∃ world trace final spent fits,
        ResourceLoopExec host pure program depth modes live test step env
          (count.denote pure.funs env).toNat 0 (initial.denote pure.funs env) world trace
          (.returned returned) final spent fits
  | _, _, .write output buffer start count, env, outcome => ∃ world trace final,
      Exec host ((Command.write output buffer start count).denote pure.funs
        (program.funs pure.funs) env) world trace outcome final
  | _, _, .exit code, env, outcome => ∃ world trace final,
      Exec host (Action.exit (code.denote pure.funs env)) world trace outcome final
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
  | write execution => exact ⟨_, _, _, execution⟩
  | exit execution => exact ⟨_, _, _, execution⟩
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
      PureContext.loopCountCost, PureContext.loopTestCost, PureContext.argumentCost, Expr.allocs,
      Var.cost, Var.ownedCost, Expr.ownedCost, Expr.mode, coerceCost, Ty.copyCost, envGet,
      Expr.denote, Args.get_cons_zero', Args.get_cons_zero, Args.get_cons_succ, Env.ofFn, argsSum,
      callCredits, ResultTy.bindEnv, loopEnv, loopModes, letPairEnv, letPairModes, modeAt,
      sysTakeLive, List.get_cons_zero, List.get_cons_succ', parseN_charge, tally_charge,
      render_charge, allocCost, Elem.width, sumBelow, UInt64.reduceToNat, Nat.add_zero,
      Nat.zero_add, ↓reduceIte, ite_self] <;>
   omega))

/-- Proves a bound on the charge of the loop's initial state, whose buffer of 4,096 bytes `charge`
would unfold byte by byte: sums the constant charge of its bytes with `sumBelow_const`. -/
local macro "init_charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.loopInitCost,
      PureContext.loopCountCost, PureContext.argumentCost, Expr.allocs, Var.cost, Var.ownedCost,
      Expr.ownedCost, Expr.mode, coerceCost, Ty.copyCost, envGet, Expr.denote, Args.get_cons_zero',
      Args.get_cons_zero, Args.get_cons_succ, Env.ofFn, argsSum, callCredits, ResultTy.bindEnv,
      letPairEnv, letPairModes, modeAt, parseN_charge, allocCost, Elem.width, sumBelow_const,
      UInt64.reduceToNat, Nat.add_zero, Nat.zero_add, Nat.mul_zero, ↓reduceIte, ite_self] <;>
   omega))

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

/-- Proves `Bounded` of a `sys` command whose call charges nothing and whose take moves its
buffer or has none. -/
local macro "sys_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (fun _ _ _ _ _ => by simp only [sysCost, PureContext.sysTakeCost]; charge)
     (fun _ _ _ _ _ => by simp only [sysCost, PureContext.sysTakeCost]; charge)))

/-- Proves `Bounded` of a command of `bind`s, `ret`s, and `sys` commands that charge nothing. -/
local macro "free_bound" : tactic => `(tactic|
  (repeat (first
    | (apply bounded_of_rule; intro _ _ rule; refine rule 0 0 (by omega) ?_ ?_)
    | (intro _ _)
    | ret_bound
    | sys_bound)))

/-- Reduces `Bounded` of an `ite` to its branches with the budget `branch` for each. -/
local macro "ite_bound " branch:term:max : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   refine rule $branch $branch (ite_cost (by charge)) (by fits) (fun _ => ?_) (fun _ => ?_)))

/-- `writeAll` charges nothing: it computes the window of its buffer in words, and each of its
passes binds the window of the bytes that remain and writes it from the borrowed buffer. -/
theorem writeAll_bounded {World : Type} {host : Host World} {depth : UInt64}
    (env : Env [Ty.bytes, Ty.word, Ty.word]) :
    Bounded host (.ofProg command.pure.program command.pure.funs) .nil depth
      (entryModes command.writeAll.func.params command.writeAll.func.modes) (fun _ => false)
      command.writeAll.func.body env 0 := by
  bind_bound 0 0
  · ret_bound
  intro _ _
  bind_bound 0 0
  · ret_bound
  intro _ _
  apply bounded_of_rule
  intro _ _ rule
  refine rule 0 (by charge) ?_ ?_
  · simp only [PureContext.loopInitFits, Bool.and_eq_true]
    exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
      Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
  refine LoopBounded.mono (loop_bounded (type := .word) (t := 0) (s := 0)
    (fun _ : UInt64 => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
  · intro index written _
    charge
  · intro index written _
    exact Expr.fits_of_depthCalls _ _ _ (by decide) _
  · intro index written _
    bind_bound 0 0
    · bind_bound 0 0
      · ret_bound
      · intro _ _
        bind_bound 0 0
        · ret_bound
        · intro _ _
          write_bound
    · intro _ _
      ite_bound 0
      · ret_bound
      · ret_bound
  · intro _ _ _ _ _
    trivial
  · simp

/-- Every run and every prefix of `main`'s body charges at most `budget` for every host whose
successful `args_sizes_get` replies ask for at most `argsLimit` bytes. -/
theorem body_bounded {World : Type} {host : Host World}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ argsLimit) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs)
      (.cons command.writeAll.func .nil) 0 [] (fun _ => false) command.main.func.body .nil
      budget := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    (inputs := []) (buffers := [])
    bound (Nat.le_refl (Bytes.allocationCost argsLimit))
  unfold budget
  generalize Bytes.allocationCost argsLimit = A at reported ⊢
  bind_bound A 21416
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments returned
  obtain ⟨errno, _, _, bytes⟩ := arguments
  letPair_free
  apply bounded_of_rule
  intro _ _ rule
  refine rule 21416 21416 (ite_cost (by charge)) (by fits) (fun _ => ?_)
    (fun _ => ?_)
  · ret_bound
  bind_bound 0 21416
  · ret_bound
  intro n returnedN
  ite_bound 21416
  · ret_bound
  bind_bound 4280 17136
  · apply bounded_of_rule
    intro _ _ rule
    refine rule 0 (by init_charge) ?_ ?_
    · simp only [PureContext.loopInitFits, Bool.and_eq_true]
      exact ⟨Expr.fits_of_depthCalls _ _ _ (by decide) _,
        Expr.fits_of_depthCalls _ _ _ (by decide) _⟩
    refine LoopBounded.mono (loop_bounded (type := stateTy) (t := 0) (s := 0)
      (fun _ => True) ?_ ?_ ?_ ?_ _ _ _ trivial) ?_
    · intro index state _
      charge
    · intro index state _
      exact Expr.fits_of_depthCalls _ _ _ (by decide) _
    · intro index state _
      obtain ⟨counts, buffer, left, errno⟩ := state
      letPair_free
      free_bound
      obtain ⟨randomErrno, randomCount, randomBuffer⟩ := ‹UInt64 × UInt64 × LeanExe.Bytes›
      letPair_free
      ite_bound 0
      · ret_bound
      · ret_bound
    · intro _ _ _ _ _
      trivial
    · simp
  intro drawn returnedLoop
  obtain ⟨counts, buffer, left, errno⟩ := drawn
  have renderBound := render_bound_command counts
  letPair_free
  ite_bound 17136
  · ret_bound
  bind_bound 17136 0
  · ret_bound
  intro output returnedOutput
  bind_bound 0 0
  · apply bounded_of_rule
    intro _ _ rule
    exact rule 0 (by charge) rfl (callBounded_here (by decide) (writeAll_bounded _))
  · intro _ _
    apply bounded_of_rule
    intro _ _ rule
    exact rule (by charge) (by fits)

end Demos.RandomHistogram
