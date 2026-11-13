import Verified.Examples.WasiSys
import Verified.Wasi.SysRule
import Verified.Wasi.SysWords
import Verified.Wasi.FunctionEntry
import Verified.FieldsArgs

/-! `_start` of `Verified.Examples.WasiSys.command` exits with an accepted status for every host
whose successful `args_sizes_get` replies ask for blocks of at most `limit` bytes, with `limit` at
most 252,640,960, every host environment satisfying `hostSpecWith host command.sysCalls`, and
every world, when the host does not trap along `main` and its exit (`total_of_bound`).  The
theorem discharges the heap, budget, and memory premises of the generated `command.total`.

The budget bounds the heap that `main` allocates (`body_bounded`).  The reflected body binds the
result of `args` and destructures it in every later expression, and `Expr.allocs` charges a copy
of an owned variable that stays live, so each use but the last copies the argument bytes, of
which a returned `args` result holds at most `limit` (`args_bytes_le`).  The result of
`randomGet 16` is copied twice in the same way, and a returned result holds at most 16 bytes
(`random_bytes_le`).  With the literal pool's 4,096 bytes, the budget fits 65,535 pages exactly
when `limit` is at most 252,640,960 (`initial_within`). -/

namespace Verified.Examples.WasiSys

open Wasm LeanExe LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi
  Verified.Wasi.Resource

/-- A bound on the heap that `main` allocates when the reporter's replies ask for blocks of at
most `limit` bytes: the block of `args` and 16 copies of the argument bytes, at most
`Bytes.allocationCost limit` each, the four results of `wordBytes` (56 bytes each), and the buffer
of `randomGet 16` and two copies of it (64 bytes each). -/
def budget (limit : Nat) : Nat := 17 * Bytes.allocationCost limit + 416

open Lean Meta in
/-- The value at `index` of an environment given as a chain of `Env.cons`. -/
private partial def envValueAt (env : Lean.Expr) (index : Nat) : MetaM (Option Lean.Expr) := do
  match (← whnfD env).getAppFnArgs with
  | (``Env.cons, #[_, _, value, rest]) =>
    if index == 0 then return some value else envValueAt rest (index - 1)
  | _ => return none

open Lean Meta Simp in
/-- Reads `Env.get env (Var.ofIndex Γ i h)` as the `i`-th value of `env` when `env` is a chain of
`Env.cons`, a definitional step.  The types of the chain's `Env.cons` nodes are those of the
commands that bound the values, such as `SysForm.reported.ty`, and the list `Γ` of the reflected
variable states them in another form, so a rewriting lemma for `Env.get` of `Env.cons` does not
match. -/
dsimproc_decl envGet (Env.get _ (Var.ofIndex _ _ _)) := fun e => do
  let (``Env.get, #[_, _, env, reference]) := e.getAppFnArgs | return .continue
  let (``Var.ofIndex, #[_, _, index, _]) := reference.getAppFnArgs | return .continue
  let some index := index.rawNatLit? <|> index.nat? | return .continue
  let some value ← envValueAt env index | return .continue
  return .done value

private theorem wordBytes_charge (env : Env [Ty.word]) :
    ((PureContext.ofProg command.pure.program command.pure.funs).callBounds 0).get FVar.here env =
      56 := by
  cases env with
  | cons word rest =>
    cases rest
    exact (command.pureSources.wordBytes.bound_eq word).trans rfl

private theorem exec_sys_returned {World α : Type} {host : Host World} {call : Call}
    {args : List Arg} {next : Reply → Action α} {world final : World} {trace : List Event}
    {value : α} (run : Exec host (.sys call args next) world trace (.returned value) final)
    (accepted : call.reject args = 0) :
    ∃ errno committed after rest, host.sys world call args (.returned errno committed) after ∧
      Exec host (next (sysReply errno committed)) after rest (.returned value) final := by
  cases run with
  | sys_reject fits => exact absurd accepted fits
  | sys_return _ permitted next => exact ⟨_, _, _, _, permitted, next⟩

private theorem exec_pure_value {World α : Type} {host : Host World} {result value : α}
    {world final : World} {trace : List Event}
    (run : Exec host (.pure result) world trace (.returned value) final) : value = result :=
  Outcome.returned.inj (exec_pure_shape run).2.1

/-- A returned `args` result holds at most `limit` bytes when every successful reply of the
reporter that `host` permits asks for a block of at most `limit` bytes: the bytes are those of
the shown region, whose size is the reporter's second word. -/
theorem args_bytes_le {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    {values : List UInt64} {world final : World} {trace : List Event}
    {value : UInt64 × UInt64 × UInt64 × LeanExe.Bytes}
    (run : Exec host (SysForm.reported.run Call.argsGet values) world trace (.returned value)
      final) :
    value.2.2.2.data.size ≤ limit := by
  obtain ⟨errno, sizes, middle, rest, reporter, next⟩ := exec_sys_returned run rfl
  split at next
  · rw [exec_pure_value next]
    exact Nat.zero_le _
  rename_i nonzero
  have zero : errno = 0 := by simpa [sysReply] using nonzero
  subst zero
  split at next
  · rw [exec_pure_value next]
    exact Nat.zero_le _
  obtain ⟨errno, got, after, rest, getter, next⟩ := exec_sys_returned next rfl
  split at next
  · rw [exec_pure_value next]
    exact Nat.zero_le _
  rename_i _ gotNonzero
  have gotZero : errno = 0 := by simpa [sysReply] using gotNonzero
  subst gotZero
  rw [exec_pure_value next]
  have shape : sizes.map (·.data.size) = [4, 4] := (host.sys_bound reporter).1
  rcases sizes with _ | ⟨count, _ | ⟨size, _ | ⟨_, _⟩⟩⟩ <;> simp at shape
  have countSmall := littleEndian_four_lt shape.1
  have sizeSmall := littleEndian_four_lt shape.2
  have asked := bound _ _ _ reporter
  simp only [reportedSize, Reply.word, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some, UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat,
    Nat.reducePow] at asked
  have gotShape : got.map (·.data.size) = [1 * (littleEndian size).toNat] := by
    have permitted := (host.sys_bound getter).1
    rw [host.sys_reports (call := Call.argsGet) reporter rfl] at permitted
    exact permitted
  rcases got with _ | ⟨shown, _ | ⟨_, _⟩⟩ <;> simp at gotShape
  simp only [SysForm.value, wordsBytesValue, sysReply, ↓reduceIte, Reply.bytes,
    List.getElem?_cons_zero, Option.getD_some]
  omega

/-- A returned `randomGet 16` result holds at most 16 bytes, the capacity of its output. -/
theorem random_bytes_le {World : Type} {host : Host World} {world final : World}
    {trace : List Event} {value : UInt64 × LeanExe.Bytes}
    (run : Exec host ((SysForm.flat 0 true).runWith Call.randomGet [16] []) world trace
      (.returned value) final) :
    value.2.data.size ≤ 16 := by
  obtain ⟨errno, committed, after, rest, permitted, next⟩ := exec_sys_returned run rfl
  rw [exec_pure_value next]
  have shape : committed.map (·.data.size) = [16] := (host.sys_bound permitted).1
  change ((sysReply errno committed).bytes 0).data.size ≤ 16
  rcases committed with _ | ⟨buffer, _ | ⟨_, _⟩⟩ <;> simp at shape
  by_cases zero : errno = 0
  · subst zero
    simp [sysReply, Reply.bytes, shape]
  · have empty : (sysReply errno [buffer]).outputs = [] := ite_eq_right zero
    simp only [Reply.bytes, empty, List.getElem?_nil, Option.getD_none]
    exact Nat.zero_le _

/-- What a run of a command with outcome `outcome` implies, for the forms whose results the charge
of `main` reads: a `ret` returns the value of its expression, a `sys` command ends as a run of its
action, and a `bind` that returns has a first command that returns and a second command that
returns the same value. -/
private def ReturnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
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
  | _, _, _, _, _ => True

private theorem returnFact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
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
  | _ => trivial

private theorem returns_fact {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {depth : UInt64} {modes : List Mode} {live : Nat → Bool} {context : List Ty}
    {result : ResultTy} {command : Command pureSigs effectSigs context result} {env : Env context}
    {value : result.denote}
    (returns : Returns host pure program depth modes live command env value) :
    ReturnFact host pure program depth modes live command env (.returned value) := by
  obtain ⟨_, _, _, _, _, run⟩ := returns
  exact returnFact run

private theorem returns_args {World : Type} {pureSigs : List Sig} {effectSigs : List EffectSig}
    {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    {pure : PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
    {modes : List Mode} {live : Nat → Bool} {context : List Ty} {env : Env context}
    {value : UInt64 × UInt64 × UInt64 × LeanExe.Bytes}
    (returns : Returns (observedHost host) pure program depth modes live
      (.sys Call.argsGet .reported [] []) env value) :
    value.2.2.2.data.size ≤ limit := by
  obtain ⟨_, _, _, execution⟩ := returns_fact returns
  exact args_bytes_le (host := observedHost host) (values := [])
    (fun _ _ _ permitted => bound _ _ _ permitted.1) execution

private theorem returns_random {World : Type} {pureSigs : List Sig}
    {effectSigs : List EffectSig} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode}
    {live : Nat → Bool} {context : List Ty} {capacity : Expr pureSigs context .word}
    {args : List (Var (.word :: context) .word)} {env : Env context}
    {value : UInt64 × LeanExe.Bytes}
    (returns : Returns host pure program depth modes live
      (.bind (.ret capacity) (.sys Call.randomGet (.flat 0 true) args [])) env value)
    (sixteen : args.map (Env.cons (capacity.denote pure.funs env) env).get = [16]) :
    value.2.data.size ≤ 16 := by
  obtain ⟨_, first, next⟩ := returns_fact returns value rfl
  have same : _ = capacity.denote pure.funs env := returns_fact first
  subst same
  obtain ⟨_, _, _, execution⟩ := returns_fact next
  change Exec host ((SysForm.flat 0 true).runWith Call.randomGet
    (args.map (Env.cons (capacity.denote pure.funs env) env).get) []) _ _ _ _ at execution
  rw [sixteen] at execution
  exact random_bytes_le execution

/-- The cost of an `if` whose branches have one budget. -/
private theorem ite_cost {c : Prop} {decision : Decidable c} {cost branch total : Nat}
    (bound : cost + branch ≤ total) : cost + @ite Nat c decision branch branch ≤ total := by
  cases decision <;> exact bound

/-- The charge of `randomGet` on the capacity 16. -/
private theorem random_charge {values : List UInt64} (sixteen : values = [16])
    (trace : List Event) : sysCostWith (.flat 0 true) Call.randomGet values [] trace ≤ 64 := by
  subst sixteen
  simp [sysCostWith, flatCapacityWith, Call.randomGet, readCost, Bytes.allocationCost]

/-- Proves a bound on the charge of an expression: evaluates its liveness tests, reads its
variables, and leaves the copies to `omega`. -/
local macro "charge" : tactic => `(tactic|
  (simp +decide only [PureContext.ownedCost, PureContext.exprCost, Expr.allocs, Var.cost,
      Expr.mode, coerceCost, Ty.copyCost, envGet, Expr.denote, Args.get_cons_zero', argsSum,
      callCredits, wordBytes_charge, Nat.add_zero, Nat.zero_add, ↓reduceIte, ite_self] <;>
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

/-- Proves `Bounded` of a flat call without an output, which charges nothing. -/
local macro "flat_bound" : tactic => `(tactic|
  (apply bounded_of_rule
   intro _ _ rule
   exact rule (fun _ _ _ _ _ => Nat.zero_le _) (fun _ _ _ _ _ => Nat.zero_le _)))

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

/-- Every run and every prefix of `main`'s body spends at most `budget limit`. -/
theorem body_bounded {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit) :
    Bounded (observedHost host) (.ofProg command.pure.program command.pure.funs) .nil 0 []
      (fun _ => false) command.main.func.body .nil (budget limit) := by
  have reported := reported_rule_observed (host := host) (call := Call.argsGet) (values := [])
    bound (Nat.le_refl (Bytes.allocationCost limit))
  unfold budget
  bind_bound (Bytes.allocationCost limit) (16 * Bytes.allocationCost limit + 416)
  · apply bounded_of_rule
    intro _ _ rule
    exact rule reported.1 reported.2
  intro arguments returned
  have argumentSize := returns_args bound returned
  obtain ⟨_, _, _, bytes⟩ := arguments
  have copy : Bytes.allocationCost bytes.data.size ≤ Bytes.allocationCost limit :=
    allocationCost_mono argumentSize
  generalize Bytes.allocationCost limit = A at copy ⊢
  ite_bound (15 * A + 416)
  · ret_bound
  bind_bound A (14 * A + 416)
  · bind_bound A 0
    · ret_bound
    · intro _ _
      write_bound
  intro _ _
  bind_bound 0 (14 * A + 416)
  · flat_bound
  intro _ _
  ite_bound (13 * A + 416)
  · ret_bound
  bind_bound (A + 56) (12 * A + 360)
  · bind_bound (A + 56) 0
    · ret_bound
    · intro _ _
      write_bound
  intro _ _
  bind_bound (A + 56) (11 * A + 304)
  · bind_bound (A + 56) 0
    · ret_bound
    · intro _ _
      write_bound
  intro _ _
  bind_bound (2 * A) (9 * A + 304)
  · bind_bound A A
    · ret_bound
    · intro _ _
      bind_bound A 0
      · ret_bound
      · intro _ _
        flat_bound
  intro _ _
  ite_bound (8 * A + 304)
  · ret_bound
  bind_bound (A + 56) (7 * A + 248)
  · bind_bound (A + 56) 0
    · ret_bound
    · intro _ _
      write_bound
  intro _ _
  bind_bound (2 * A) (5 * A + 248)
  · bind_bound A A
    · ret_bound
    · intro _ _
      bind_bound A 0
      · ret_bound
      · intro _ _
        flat_bound
  intro _ _
  ite_bound (4 * A + 248)
  · ret_bound
  bind_bound (A + 56) (3 * A + 192)
  · bind_bound (A + 56) 0
    · ret_bound
    · intro _ _
      write_bound
  intro _ _
  bind_bound (A + 64) (2 * A + 128)
  · bind_bound A 64
    · ret_bound
    · intro capacity returned
      have sixteen : capacity = (16 : UInt64) := returns_fact returned
      subst sixteen
      apply bounded_of_rule
      intro _ _ rule
      exact rule (fun _ trace _ _ _ => random_charge rfl trace)
        (fun _ trace _ _ _ => random_charge rfl trace)
  intro random returned
  have randomSize := returns_random returned rfl
  obtain ⟨_, randomBytes⟩ := random
  have randomCopy : Bytes.allocationCost randomBytes.data.size ≤ 64 :=
    allocationCost_mono randomSize
  ite_bound (A + 64)
  · ret_bound
  bind_bound (A + 64) 0
  · bind_bound (A + 64) 0
    · ret_bound
    · intro _ _
      write_bound
  intro _ _
  ret_bound

/-- Every prefix of a call of `main` spends at most `budget limit`. -/
theorem call_prefix_bound {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    (world : Observed World) :
    CallPrefixBound (observedHost host) (.ofProg command.pure.program command.pure.funs)
      command.program .here 0 .nil world (budget limit) := by
  intro trace residual final spent fits progress
  exact call_prefix_rule (budget limit) progress rfl ((body_bounded bound).2 world)

/-- The budget fits the heap above the literal pool's 4,096 bytes when `limit` is at most
252,640,960: 4,096 bytes, 17 blocks of 252,641,008 bytes, and 416 bytes are 4,294,901,648 bytes,
at most the 4,294,901,760 bytes of 65,535 pages, and the limit 252,640,961 exceeds them. -/
theorem initial_within {World : Type} (world : Observed World) {limit : Nat}
    (small : limit ≤ 252640960) :
    (initialStaticHeap command.literalPool).Within
      (PureTransport.erase (compileInitialStoreWith command.sysCalls command.pure.module
        command.program command.entries command.mainEntry command.literalPool world))
      command.pure.module (budget limit) := by
  have cost := allocationCost_mono small
  have largest : Bytes.allocationCost 252640960 = 252641008 := by decide
  change 4096 + budget limit ≤ 65536 * 65535
  unfold budget
  omega

/-- `_start` exits with an accepted status for every host whose successful `args_sizes_get`
replies ask for blocks of at most `limit` bytes, with `limit` at most 252,640,960, every host
environment satisfying `hostSpecWith host command.sysCalls`, and every world, when the host does
not trap along `main` and its exit. -/
theorem total_of_bound {World : Type} {host : Host World} {limit : Nat}
    (bound : ∀ world outputs after,
      host.sys world Call.argsGet.reporterCall [] (.returned 0 outputs) after →
        reportedSize outputs ≤ limit)
    (small : limit ≤ 252640960) (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies command.module (hostSpecWith host command.sysCalls))
    (safe : host.NoTrapsAlong (main.bind fun status => (Action.exit status : Action Unit))
      world.world) :
    ∃ fuelBound, ∀ fuel ≥ fuelBound,
      AcceptedExit host (main.bind fun status => (Action.exit status : Action Unit)) world
        (run fuel command.module (Wrappers.effectIndexWith command.sysCalls command.pure.module 1)
          (compileInitialStoreWith command.sysCalls command.pure.module command.program
            command.entries command.mainEntry command.literalPool world) [] targetHost) := by
  have initialized := command.initial world
  exact command.total valid initialized.1 rfl Separate.nil
    ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩ (fun _ membership => nomatch membership)
    initialized.2.1 (fun _ => ⟨initial_within world small, call_prefix_bound bound world⟩) safe

end Verified.Examples.WasiSys
