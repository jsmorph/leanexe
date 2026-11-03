import Demos.OrderBook.Bound
import Demos.OrderBook.ProcessSizes
import Verified.Wasi.ResourceRules

/-! The allocation charges of the compiled process's `begin` and steps.  `begin` builds the seven
arrays of the empty book.  A write step allocates the remaining output and copies the state, and a
stopping step copies the state.  A read step allocates the read buffer and either copies the state
at an errno or runs a batch: the words of the batch, the copies of the seven arrays into `run`,
`run`'s generated bound, the carry after the batch, and the event bytes.  The charge of a read step
holds for every reply of at most 4,096 bytes, so for a batch that need not lie in the input, and it
cannot depend on the input's records.  It takes `run`'s generated bound on any batch of at most 518
words from any book whose arrays have the program's sizes as a term `R` with `RunBound R`, and
`runBound_74` gives `RunBound (Bound.runBoundSized 74)` from the closed form of
[the bound of `run`](Bound.lean), which needs neither the invariant nor room for the next ids. -/

namespace Demos.OrderBook.Process

open _root_.Verified _root_.Verified.Wasi _root_.Verified.Wasi.Resource
open LeanExe LeanExe.Wasi Refinement
open Demos.StreamFold (StreamPosition)

/-- `R` bounds the generated bound of `run` on every batch of at most 518 words, which holds at
most 74 records, from every book whose seven arrays have the program's sizes. -/
def RunBound (R : Nat) : Prop :=
  ∀ (b : Program.Book) (ws : Array UInt64),
    Program.sizes b = (4097, 4097, 4097, 4097, 4097, 2048, 2048) → ws.size ≤ 518 →
    io.pureSources.run.bound (⟨b.oid⟩, ⟨b.acct⟩, ⟨b.qty⟩, ⟨b.lvl⟩, ⟨b.nxt⟩, ⟨b.head⟩, ⟨b.tail⟩,
      b.nextId, b.count, ws) ≤ R

/-- The closed form of `run`'s bound on 74 records from any book of the program's sizes applies to
this compilation's equations. -/
theorem runBound_74 : RunBound (Bound.runBoundSized 74) := by
  intro b ws sizes small
  exact Bound.run_bound_le_sized
    ⟨io.pureSources.emit.cost_eq, io.pureSources.fillArrays.cost_eq,
      io.pureSources.submitArrays.cost_eq, io.pureSources.stepArrays.cost_eq,
      io.pureSources.run.cost_eq, io.pureSources.run.bound_eq⟩
    sizes ws (by omega) (by omega)

/-- The book of a state with the sizes of `Sized` has the program's array sizes. -/
theorem Sized.book_sizes {s : State} (sized : Sized s) :
    Program.sizes (book s) = (4097, 4097, 4097, 4097, 4097, 2048, 2048) := by
  simp only [Program.sizes, book, sized.oid, sized.acct, sized.qty, sized.lvl, sized.nxt,
    sized.head, sized.tail]

/-- The flags of the pure program's functions, from `afterRead` back to `emit`.  The kernel
computes them once, so that the charges of the effect bodies read a list rather than evaluate
`Prog.flags`, which the elaborator would do over the bodies of every earlier function at each
call. -/
theorem flags_toList : io.pure.program.flags.toList =
    [([false, false], false), ([false, false], false), ([false], false),
      ([false, false, false, false], false), ([false, false, false], false), ([false], false),
      ([false, false, false], false), ([], false),
      ([true, true, true, true, true, true, true, false, false, false], false),
      ([true, true, true, true, true, true, true, false, false, true, false, false], false),
      ([true, true, true, true, true, true, true, false, false, true, false, false, false, false,
        false, false], false),
      ([true, true, true, true, true, true, true, false, false, true, false, false, false, false,
        false], false),
      ([false, false, false], false), ([false, false], false),
      ([false, false, false, false], false), ([false], false), ([false, false], false),
      ([true, false, false, false, false, false, false, false], true)] := by
  decide +kernel

theorem remainingOutput_bound_le (s : State) (pending : s.written < s.output.size) :
    io.pureSources.remainingOutput.bound s ≤ Bytes.allocationCost s.output.data.size := by
  rw [io.pureSources.remainingOutput.bound_eq]
  apply allocationCost_mono
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt pending)]
  have size : s.output.size.toNat ≤ s.output.data.size := by
    simp only [LeanExe.Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

theorem afterWrite_bound_le (s : State) (reply : WriteResult) :
    io.pureSources.afterWrite.bound (s, reply) ≤ stateTy.copyCost (sourceState s) := by
  rw [io.pureSources.afterWrite.bound_eq, state_copyCost]
  simp only [LeanExe.Pipeline.Flat.flat, Ty.copyCost, blockCost_eq, copyBytes]
  split
  · omega
  · split <;> omega

/-- The charge of a batch from `s`, with `R` for `run`'s bound: the batch's words, the copies of
the seven arrays into `run`, `R`, the carry after the batch, and the event bytes. -/
def batchCharge (R : Nat) (s : State) : Nat :=
  blockCost 518 + (blockCost s.oid.size + blockCost s.acct.size + blockCost s.qty.size +
    blockCost s.lvl.size + blockCost s.nxt.size + blockCost s.head.size + blockCost s.tail.size) +
  R + Bytes.allocationCost (s.carry.data.size + 4096) + Bytes.allocationCost (8 * (7 * 5122 * 74))

theorem runWords_bound_le {R : Nat} {s : State}
    (runLe : ∀ ws : Array UInt64, ws.size ≤ 518 →
      io.pureSources.run.bound (⟨s.oid⟩, ⟨s.acct⟩, ⟨s.qty⟩, ⟨s.lvl⟩, ⟨s.nxt⟩, ⟨s.head⟩, ⟨s.tail⟩,
        s.nextId, s.count, ws) ≤ R)
    (carrySmall : s.carry.data.size < 56) (input : Bytes) (count : UInt64) (eof : Bool)
    (inputSize : input.data.size ≤ 4096)
    (countLe : 8 * count.toNat ≤ s.carry.data.size + input.data.size) :
    io.pureSources.runWords.bound (s, input, count, eof) ≤ batchCharge R s := by
  have countSmall : count.toNat ≤ 518 := by omega
  have wordsSize : (wordsOf s.carry input count).size ≤ 518 := by
    rw [wordsOf_size]
    exact countSmall
  have runCost := runLe (wordsOf s.carry input count) wordsSize
  rw [io.pureSources.run.bound_eq] at runCost
  have events := run_batch_out_size (book s) (wordsOf s.carry input count) wordsSize
  change (Program.run s.oid s.acct s.qty s.lvl s.nxt s.head s.tail s.nextId s.count
    (wordsOf s.carry input count)).2.size ≤ _ at events
  have carryNat : s.carry.size.toNat = s.carry.data.size :=
    Bytes.size_toNat s.carry (Nat.lt_of_lt_of_le carrySmall (by decide))
  have inputNat : input.size.toNat = input.data.size :=
    Bytes.size_toNat input (Nat.lt_of_le_of_lt inputSize (by decide))
  have startNat : (8 * count).toNat = 8 * count.toNat := by
    rw [UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  have sumNat : (s.carry.size + input.size).toNat = s.carry.data.size + input.data.size := by
    rw [UInt64.toNat_add, carryNat, inputNat]
    exact Nat.mod_eq_of_lt (by omega)
  have keptNat : (s.carry.size + input.size - 8 * count).toNat ≤
      s.carry.data.size + input.data.size := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [startNat, sumNat]; omega)),
      startNat, sumNat]
    omega
  have eventsNat : (8 * (Program.run s.oid s.acct s.qty s.lvl s.nxt s.head s.tail s.nextId s.count
      (wordsOf s.carry input count)).2.size.toUInt64).toNat ≤ 8 * (7 * 5122 * 74) := by
    rw [UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    have := toUInt64_toNat_le (Program.run s.oid s.acct s.qty s.lvl s.nxt s.head s.tail s.nextId
      s.count (wordsOf s.carry input count)).2.size
    exact Nat.le_trans (Nat.mod_le _ _) (by omega)
  have kept := allocationCost_mono (Nat.le_trans keptNat (Nat.add_le_add_left inputSize _))
  have eventCost := allocationCost_mono eventsNat
  rw [io.pureSources.runWords.bound_eq, io.pureSources.wordsOf.bound_eq,
    io.pureSources.tailBytes.bound_eq, io.pureSources.eventBytes.bound_eq]
  have wordsCost := blockCost_le_of_le countSmall
  unfold batchCharge
  omega

/-- The bound of `afterRead` for every reply of at most 4,096 bytes: a copy of the state at an
errno and a batch otherwise. -/
theorem afterRead_bound_le {R : Nat} {s : State}
    (runLe : ∀ ws : Array UInt64, ws.size ≤ 518 →
      io.pureSources.run.bound (⟨s.oid⟩, ⟨s.acct⟩, ⟨s.qty⟩, ⟨s.lvl⟩, ⟨s.nxt⟩, ⟨s.head⟩, ⟨s.tail⟩,
        s.nextId, s.count, ws) ≤ R)
    (carrySmall : s.carry.data.size < 56) (reply : ReadResult)
    (size : reply.bytes.data.size ≤ 4096) :
    io.pureSources.afterRead.bound (s, reply) ≤
      stateTy.copyCost (sourceState s) + batchCharge R s := by
  have carryNat : s.carry.size.toNat = s.carry.data.size :=
    Bytes.size_toNat s.carry (Nat.lt_of_lt_of_le carrySmall (by decide))
  have bytesNat : reply.bytes.size.toNat = reply.bytes.data.size :=
    Bytes.size_toNat reply.bytes (Nat.lt_of_le_of_lt size (by decide))
  rw [io.pureSources.afterRead.bound_eq]
  split
  · rw [state_copyCost]
    simp only [LeanExe.Pipeline.Flat.flat, Ty.copyCost, blockCost_eq, copyBytes]
    omega
  · split
    · have emptySize : Bytes.empty.data.size = 0 := rfl
      have countNat : (s.carry.size / 8).toNat = s.carry.data.size / 8 := by
        rw [UInt64.toNat_div, carryNat]
        rfl
      have batch := runWords_bound_le runLe carrySmall Bytes.empty (s.carry.size / 8) true
        (by rw [emptySize]; decide) (by rw [countNat, emptySize]; omega)
      omega
    · have countNat : (7 * ((s.carry.size + reply.bytes.size) / 56)).toNat =
          7 * ((s.carry.data.size + reply.bytes.data.size) / 56) := by
        rw [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, carryNat, bytesNat]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (by omega : s.carry.data.size + reply.bytes.data.size < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega)]
      have batch := runWords_bound_le runLe carrySmall reply.bytes
        (7 * ((s.carry.size + reply.bytes.size) / 56)) false size (by rw [countNat]; omega)
      omega

/-- The charge of `begin`: the arrays of the empty book. -/
def beginCharge : Nat := io.pureSources.initial.bound ()

theorem beginCharge_eq : beginCharge = 197040 := by
  unfold beginCharge
  rw [io.pureSources.initial.bound_eq]
  decide

section Bodies

local notation "pureContext" => Resource.PureContext.ofProg io.pure.program io.pure.funs

open Lean Meta in
/-- The value at index `i` of an environment given as a chain of `Env.cons`. -/
private partial def envValueAt (env : Lean.Expr) (i : Nat) : MetaM (Option Lean.Expr) := do
  match (← whnfR env).getAppFnArgs with
  | (``Env.cons, #[_, _, v, rest]) => if i == 0 then return some v else envValueAt rest (i - 1)
  | _ => return none

open Lean Meta Simp in
/-- Reads `Env.get env (Var.ofIndex Γ i h)` as the `i`-th value of `env` when `env` is a chain of
`Env.cons`, a definitional step.  The effect bodies destructure the state's 13 fields, and each
level of the environment holds the previous level twice, so the elaborator's conversion of a
call's arguments to the state unfolds a tree exponential in the depth, while `simp` applies this
step once to each shared subterm. -/
simproc ↓ envGetOfIndex (Env.get _ (Var.ofIndex _ _ _)) := fun e => do
  let (``Env.get, #[_, _, env, x]) := e.getAppFnArgs | return .continue
  let (``Var.ofIndex, #[_, _, i, _]) := x.getAppFnArgs | return .continue
  let some n := i.rawNatLit? <|> i.nat? | return .continue
  let some v ← envValueAt env n | return .continue
  return .done { expr := v }

/-- Proves that a condition of an effect body has enough frames: it calls no function that takes
the call depth. -/
local macro "condition_fits" : tactic =>
  `(tactic| exact Expr.fits_of_depthCalls _ _ _ (by decide) _)

/-- Rewrites the values of an effect body's destructured state to the fields of the state. -/
local macro "read_state" : tactic =>
  `(tactic| try simp only [Expr.denote, Env.ofFn, Args.get_cons_zero, Args.get_cons_zero',
    Args.get_cons_succ, Args.denote, envGetOfIndex, sourceState])

/-- An `if` whose branches are at most 0, for any decision procedure.  The cost of the stopping
branch's status is such an `if`, whose instance still holds the effect body's environment, so
`ite_self` and `split`, which rebuild the instance, do not apply. -/
theorem ite_le_zero {c : Prop} {decision : Decidable c} {a b : Nat} (left : a ≤ 0) (right : b ≤ 0) :
    @ite Nat c decision a b ≤ 0 := by
  cases decision
  · exact right
  · exact left

theorem stepModes : entryModes io.step.func.params io.step.func.modes = [.borrowed] := by
  decide

theorem readModes : entryModes io.readStep.func.params io.readStep.func.modes = [.borrowed] := by
  decide

theorem writeModes : entryModes io.writeStep.func.params io.writeStep.func.modes = [.borrowed] := by
  decide

/-- The charge of the write step from `s`: the remaining output and a copy of the state. -/
def writeCharge (s : State) : Nat :=
  io.pureSources.remainingOutput.bound s + stateTy.copyCost (sourceState s)

/-- The charge of the read step from `s`: the read buffer, and a copy of the state or a batch. -/
def readCharge (R : Nat) (s : State) : Nat :=
  Verified.Wasi.readCost 4096 + (stateTy.copyCost (sourceState s) + batchCharge R s)

/-- The charge of the step from `s` when no output remains: a copy of the state at EOF and a read
otherwise. -/
def restCharge (R : Nat) (s : State) : Nat :=
  if s.eof = true then stateTy.copyCost (sourceState s) else readCharge R s

/-- The charge of the step from `s`, by its branches. -/
def stepBudget (R : Nat) (s : State) : Nat :=
  if s.written < s.output.size then writeCharge s else restCharge R s

set_option maxHeartbeats 1000000 in
theorem writeStep_bounded {World : Type} (host : Host World) (depth : UInt64) (s : State) :
    Bounded host pureContext .nil depth
      (entryModes io.writeStep.func.params io.writeStep.func.modes) (fun _ => false)
      io.writeStep.func.body (.cons (sourceState s) .nil) (writeCharge s) := by
  rw [writeModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (io.pureSources.remainingOutput.bound s) (stateTy.copyCost (sourceState s))
    (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule (io.pureSources.remainingOutput.bound s) 0 (Nat.le_of_eq (Nat.add_zero _)) ?_ ?_
    · apply bounded_of_rule
      intro spent fits rule
      refine rule ?_ rfl
      simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
        Expr.allocs, Var.cost, Expr.mode, argsSum, callCredits, Flags.params, flags_toList,
        FVar.index, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
      read_state
      show io.pureSources.remainingOutput.bound s ≤ _
      exact Nat.le_refl _
    · intro value _
      apply bounded_of_rule
      intro spent fits rule
      exact rule
  · intro value _
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, Flags.params, flags_toList, FVar.index,
      Args.get_cons_zero', Args.get_cons_succ, Ty.copyCost_of_scalar, ↓reduceIte, Nat.add_zero,
      Nat.zero_add, coerceCost]
    read_state
    show io.pureSources.afterWrite.bound (s, ⟨value.1, value.2⟩) ≤ _
    exact afterWrite_bound_le s _

set_option maxHeartbeats 1000000 in
theorem readStep_bounded {World : Type} (host : Host World) (depth : UInt64) {R : Nat} {s : State}
    (runLe : ∀ ws : Array UInt64, ws.size ≤ 518 →
      io.pureSources.run.bound (⟨s.oid⟩, ⟨s.acct⟩, ⟨s.qty⟩, ⟨s.lvl⟩, ⟨s.nxt⟩, ⟨s.head⟩, ⟨s.tail⟩,
        s.nextId, s.count, ws) ≤ R)
    (carrySmall : s.carry.data.size < 56) :
    Bounded host pureContext (.cons io.writeStep.func .nil) depth
      (entryModes io.readStep.func.params io.readStep.func.modes) (fun _ => false)
      io.readStep.func.body (.cons (sourceState s) .nil) (readCharge R s) := by
  rw [readModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (Verified.Wasi.readCost 4096) _ (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp +decide only [PureContext.readCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add]
    read_state
    show Verified.Wasi.readCost 4096 ≤ _
    exact Nat.le_refl _
  · intro value returns
    have size : value.2.data.size ≤ 4096 := Returns.read_size returns
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, Flags.params, flags_toList, FVar.index,
      ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
    read_state
    show io.pureSources.afterRead.bound (s, ⟨value.1, value.2⟩) ≤ _
    exact afterRead_bound_le runLe carrySmall ⟨value.1, value.2⟩ size

set_option maxHeartbeats 4000000 in
theorem step_body_bounded {World : Type} (host : Host World) {R : Nat} {s : State}
    (runLe : ∀ ws : Array UInt64, ws.size ≤ 518 →
      io.pureSources.run.bound (⟨s.oid⟩, ⟨s.acct⟩, ⟨s.qty⟩, ⟨s.lvl⟩, ⟨s.nxt⟩, ⟨s.head⟩, ⟨s.tail⟩,
        s.nextId, s.count, ws) ≤ R)
    (carrySmall : s.carry.data.size < 56) :
    Bounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil)) 0
      (entryModes io.step.func.params io.step.func.modes) (fun _ => false) io.step.func.body
      (.cons (sourceState s) .nil) (stepBudget R s) := by
  rw [stepModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (writeCharge s) (restCharge R s) ?_ rfl ?_ ?_
  · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost, ↓reduceIte,
      Nat.add_zero, Nat.zero_add]
    read_state
    show (if decide (s.written < s.output.size) = true then writeCharge s
      else restCharge R s) ≤ stepBudget R s
    simp only [stepBudget, decide_eq_true_eq, Nat.le_refl]
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (writeCharge s) ?_ rfl ?_
    · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
        argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      exact Nat.le_refl _
    · read_state
      show CallBounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil))
        (.there .here) (0 + 1) (.cons (sourceState s) .nil) (writeCharge s)
      exact callBounded_there (callBounded_here (by decide) (writeStep_bounded host _ s))
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (stateTy.copyCost (sourceState s)) (readCharge R s) ?_ (by condition_fits) ?_ ?_
    · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost,
        ↓reduceIte, Nat.add_zero, Nat.zero_add, ite_self, coerceCost]
      read_state
      show (if (if s.eof = true then true else !true) = true then stateTy.copyCost (sourceState s)
        else readCharge R s) ≤ restCharge R s
      by_cases eof : s.eof = true <;> simp [eof, restCharge]
    · intro _
      apply bounded_of_rule
      intro spent fits rule
      refine rule ?_ (by condition_fits)
      simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
        Expr.allocs, Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
      read_state
      simp only [Ty.copyCost, stateTy]
      refine Nat.le_trans (Nat.add_le_add_right (ite_le_zero (Nat.le_refl _) (Nat.le_refl _)) _) ?_
      omega
    · intro _
      apply bounded_of_rule
      intro spent fits rule
      refine rule (readCharge R s) ?_ rfl ?_
      · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
          argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
        exact Nat.le_refl _
      · read_state
        show CallBounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil))
          .here (0 + 1) (.cons (sourceState s) .nil) (readCharge R s)
        exact callBounded_here (by decide) (readStep_bounded host _ runLe carrySmall)

/-- The step from `s` uses at most `stepBudget R s` and has enough frames. -/
theorem step_bounded {World : Type} (host : Host World) {R : Nat} {s : State}
    (runLe : ∀ ws : Array UInt64, ws.size ≤ 518 →
      io.pureSources.run.bound (⟨s.oid⟩, ⟨s.acct⟩, ⟨s.qty⟩, ⟨s.lvl⟩, ⟨s.nxt⟩, ⟨s.head⟩, ⟨s.tail⟩,
        s.nextId, s.count, ws) ≤ R)
    (carrySmall : s.carry.data.size < 56) :
    CallBounded host pureContext io.program entry.step 0 (.cons (sourceState s) .nil)
      (stepBudget R s) :=
  callBounded_there (callBounded_here (by decide) (step_body_bounded host runLe carrySmall))

set_option maxHeartbeats 1000000 in
/-- The entry of `initial` in the bound table that the effect bodies read: the builds of the seven
arrays. -/
theorem initial_entry :
    ((Resource.PureContext.ofProg io.pure.program io.pure.funs).callBounds 0).get
      FVar.here.there.there.there.there.there.there.there Env.nil = 197040 := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem begin_bounded {World : Type} (host : Host World) :
    CallBounded host pureContext io.program entry.begin 0 .nil beginCharge := by
  apply callBounded_here (by decide)
  apply bounded_of_rule
  intro spent fits rule
  refine rule ?_ rfl
  simp only [PureContext.ownedCost, PureContext.exprCost, Expr.allocs, Expr.mode, argsSum,
    callCredits, Mode.join, Ty.scalar, Bool.false_and, Bool.and_false, Bool.false_eq_true, and_true,
    reduceCtorEq, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost, Env.ofFn, Ty.copyCost]
  exact Nat.le_of_eq (initial_entry.trans beginCharge_eq.symm)

theorem begin_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host pureContext io.program entry.begin 0 .nil world beginCharge :=
  (begin_bounded host).2 world

end Bodies

/-- A bound on the charge of every step from a state with the sizes of `Sized`, with `R` for
`run`'s bound on a batch. -/
def stepCharge (R : Nat) : Nat := copyLimit + R + 21435213

theorem stepBudget_le {R : Nat} {s : State} (sized : Sized s) : stepBudget R s ≤ stepCharge R := by
  have copy := sized.copyCost
  have output := allocationCost_le s.output.data.size
  have carry := allocationCost_le (s.carry.data.size + 4096)
  have events := allocationCost_le (8 * (7 * 5122 * 74))
  have readFull : Verified.Wasi.readCost 4096 = 4144 := by decide
  have := sized.carry
  have := sized.output
  have limit : outputLimit = 16982112 := by decide
  unfold stepBudget restCharge
  split
  · rename_i pending
    have remaining := remainingOutput_bound_le s pending
    unfold writeCharge stepCharge
    omega
  · split
    · unfold stepCharge
      omega
    · unfold readCharge batchCharge stepCharge
      simp only [blockCost_eq, sized.oid, sized.acct, sized.qty, sized.lvl, sized.nxt, sized.head,
        sized.tail]
      omega

/-- From a state with the sizes of `Sized`, when `RunBound R` holds, the step uses at most
`stepCharge R`. -/
theorem step_prefix_bound {World : Type} (host : Host World) {R : Nat} (runBound : RunBound R)
    {s : State} (sized : Sized s) (world : World) :
    CallPrefixBound host (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program
      entry.step 0 (.cons (sourceState s) .nil) world (stepCharge R) :=
  ((step_bounded host (fun ws small => runBound (book s) ws sized.book_sizes small)
    sized.carry).mono (stepBudget_le sized)).2 world

end Demos.OrderBook.Process
