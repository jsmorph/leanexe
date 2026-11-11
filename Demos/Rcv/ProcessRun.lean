import Demos.Rcv.ProcessCorrect
import Demos.Rcv.ProcessSizes
import Demos.StreamFold.Observed
import Verified.Wasi.ProcessCode
import Verified.Wasi.ProcessCorrect
import Verified.Wasi.ProcessNative
import Verified.Wasi.ProcessTotalCorrect
import Verified.Wasi.ProcessEntryProofs
import LeanExe.Encoding.FormCheck

/-! The runs of a compiled tabulator's process, for the Oakland process of
`Demos/Rcv/ProcessProof.lean` and the Maine process of `Demos/Rcv/Maine/ProcessProof.lean`, which
share the state, the steps, and the form of `begin` and differ in the report function and the
compiled program.  `Compiled start` bundles a program compiled by `verified_compile_wasi` whose
entry is `processEntry` of its `begin` and `step`, with the facts that `compiled_process_run` and
`compiled_process_total_run` take about it and the relations of its `begin` and `step` to the
native `start` and `step`.

`Compiled.implements` states that every modeled run of the module that completes without
exhausting Talos fuel matches the native process.  A control ghost pairs the native step result
with the host's ghost, and its rank orders the running flag before the rank of
`ProcessControl`.  `Compiled.target_terminates` applies `compiled_process_total_run`: the module
exits with the status `code` when the host makes progress, the native `start` returns a state that
stops with `code` or runs under an invariant that each step keeps, and the charges of `begin` and
of every reached step bound their typed resource prefixes and fit the memory with the copies of
the state.  `Compiled.terminates_of_room` and `Compiled.exits_long_of_room` state, for a process
whose `start` is `beginWith tab`, that the module exits with status 0 after writing exactly the
output of an input of at most `limit` bytes, or with status `tooLong` after writing nothing for a
longer input, from a store with room for the charge of `begin` and a copy of a state. -/

namespace Demos.Rcv.Process

open Wasm _root_.Verified _root_.Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost StreamProgress observedStreamRep stdoutWords
  byteWords)

/-! ## The compiled process -/

/-- The entry of a tabulator's process: the compiled `begin` and `step` over the state type
`stateTy`. -/
def processEntry {effectSigs : List EffectSig}
    (beginVar : EffectVar effectSigs ⟨"begin", [], [], .value (processResultTy stateTy)⟩)
    (stepVar :
      EffectVar effectSigs ⟨"step", [stateTy], [.borrowed], .value (processResultTy stateTy)⟩) :
    ProcessEntry effectSigs :=
  { state := stateTy
    beginName := "begin"
    stepName := "step"
    begin := beginVar
    step := stepVar }

theorem compactable : stateTy.compactable = true := by decide

theorem compactForm : Encoding.ProgramForm (processCompaction stateTy) :=
  Encoding.checkProgramForm_sound (by decide +kernel)

/-- A program compiled by `verified_compile_wasi` whose entry is `processEntry beginVar stepVar`,
with the facts about it that `compiled_process_run` and `compiled_process_total_run` take, and
the relations of its `begin` to the native `start` and of its `step` to the native `step`. -/
structure Compiled (start : Action (ProcessStep State)) where
  pureSigs : List Sig
  effectSigs : List EffectSig
  source : Wasm.Module
  pure : Resource.PureContext pureSigs
  program : EffectProg pureSigs effectSigs
  beginVar : EffectVar effectSigs ⟨"begin", [], [], .value (processResultTy stateTy)⟩
  stepVar : EffectVar effectSigs ⟨"step", [stateTy], [.borrowed], .value (processResultTy stateTy)⟩
  pool : Bytes.LiteralPool
  calls : CostEffectCalls source
    (compileProcess source program (processEntry beginVar stepVar) pool) pure program pool
  runtime : Runtime source
  profile : Relocation.Profile source
  compactClosed :
    Relocation.programClosed source.funcs.length (processCompaction stateTy) = true
  poolScratch : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch
  beginRelated : Action.Rel (ProcessStep.Rel (fun native flat => flat = sourceState native)) start
    ((processEntry beginVar stepVar).beginAction (program.funs pure.funs))
  stepRelated : LeanExe.Wasi.Process.Rel (fun native flat => flat = sourceState native) process
    ⟨sourceState initial, (processEntry beginVar stepVar).action (program.funs pure.funs)⟩

namespace Compiled

variable {start : Action (ProcessStep State)} (c : Compiled start)

def entry : ProcessEntry c.effectSigs := processEntry c.beginVar c.stepVar

/-- The command module. -/
def module : Wasm.Module := compileProcess c.source c.program c.entry c.pool

/-- The index of `_start`. -/
def startIndex : Nat := c.entry.startIndex c.source

/-- The process of the compiled `step`, from the state of `initial`. -/
def sourceProcess : LeanExe.Wasi.Process stateTy.denote :=
  ⟨sourceState initial, c.entry.action (c.program.funs c.pure.funs)⟩

theorem source_run {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (initial : Store (Observed World)) (heap : Heap) (fuel : Nat)
    (valid : targetHost.Satisfies c.module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : c.pool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap c.module 0 ≤ 65535)
    (completed : run fuel c.module c.startIndex initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) (c.entry.beginAction (c.program.funs c.pure.funs))
      c.sourceProcess initial.host (run fuel c.module c.startIndex initial [] targetHost) :=
  compiled_process_run c.program c.entry c.pool c.calls c.runtime c.profile compactable
    compactForm c.compactClosed (fun _ => rfl) valid at_ free static c.poolScratch cap completed

/-- Every modeled run of the module from a store with an allocator at `heap`, the literal pool,
and a memory cap of at most 65,535 pages, under a host that satisfies `hostSpec host`, that
completes without exhausting its fuel, matches a run of the native process from `initial`. -/
theorem implements {World : Type} (host : Host World) (targetHost : HostEnv (Observed World))
    (initial : Store (Observed World)) (heap : Heap) (fuel : Nat)
    (valid : targetHost.Satisfies c.module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : c.pool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap c.module 0 ≤ 65535)
    (completed : run fuel c.module c.startIndex initial [] targetHost ≠ .OutOfFuel) :
    ProcessEntryRunResult (observedHost host) start process initial.host
      (run fuel c.module c.startIndex initial [] targetHost) :=
  (c.source_run host targetHost initial heap fuel valid at_ free static cap
    completed).transport_back c.stepRelated c.beginRelated

end Compiled

/-- The reflected result of a native step result. -/
def sourceResult (value : ProcessStep State) : (processResultTy stateTy).denote :=
  processValue stateTy ⟨value.running, value.status, sourceState value.state⟩

/-- A reflected function that returns `sourceResult` of the native result, followed by
`processNative`, relates to the native action on the state's tuple. -/
theorem relatedResult {native : Action (ProcessStep State)}
    {source : Action (processResultTy stateTy).denote}
    (reflected : Action.Rel (fun native flat => flat = sourceResult native) native source) :
    Action.Rel (ProcessStep.Rel (fun native flat => flat = sourceState native)) native
      (source.bind fun value => .pure (processNative stateTy value)) := by
  have related := reflected.bind
    (results := ProcessStep.Rel (fun native flat => flat = sourceState native))
    (leftNext := Action.pure) (rightNext := fun value => .pure (processNative stateTy value))
    (fun native flat same => by
      subst flat
      exact .pure (by simp only [sourceResult, processNative_value]; exact ⟨rfl, rfl, rfl⟩))
  simpa only [Action.bind_pure] using related

/-! ## The control ghost -/

abbrev ControlGhost (Ghost : Type) := ProcessStep State × Ghost

abbrev controlOrder : WellFoundedRelation (Nat × Rank) := Prod.lex Nat.lt_wfRel rankOrder

def controlRank (zeroWrites : Ghost → Nat) (ghost : ControlGhost Ghost) : Nat × Rank :=
  (if ghost.1.running then 1 else 0, rank zeroWrites ghost.1.state ghost.2)

def ControlLt (zeroWrites : Ghost → Nat) : ControlGhost Ghost → ControlGhost Ghost → Prop :=
  InvImage controlOrder.rel (controlRank zeroWrites)

theorem control_wellFounded (zeroWrites : Ghost → Nat) :
    WellFounded (ControlLt zeroWrites) :=
  InvImage.wf (controlRank zeroWrites) controlOrder.wf

/-- The ghost's native state is related to the compiled state, safe, and represented with the
world, its status is `code` when it stops, and `Inv` holds of it and its ghost while it runs. -/
def ControlRep (code : UInt64) (rep : Ghost → World → Prop) (Inv : State → Ghost → Prop)
    (ghost : ControlGhost Ghost) (current : ProcessStep stateTy.denote) (world : World) : Prop :=
  ProcessStep.Rel (fun native flat => flat = sourceState native) ghost.1 current ∧
    Safe ghost.1.state ∧ rep ghost.2 world ∧
    (ghost.1.running = false → ghost.1.status = code) ∧
    (ghost.1.running = true → Inv ghost.1.state ghost.2)

/-- Each step from a safe state where `Inv` holds returns a state whose ghost is represented with
the final world and, while the process runs, satisfies `Inv` at a lower rank. -/
def StepAdvances {World Ghost : Type} (host : Host World) (rep : Ghost → World → Prop)
    (zeroWrites : Ghost → Nat) (Inv : State → Ghost → Prop) : Prop :=
  ∀ {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State}, Safe s → Inv s ghost → rep ghost world →
    LeanExe.Wasi.Exec host (step s) world trace (.returned next) final →
    ∃ nextGhost, rep nextGhost final ∧
      (next.running = true → Inv next.state nextGhost ∧
        RankLt (rank zeroWrites next.state nextGhost) (rank zeroWrites s ghost))

/-- What every run of the native `start` returns: a safe state with a represented ghost, which
stops with `code` or runs under `Inv`. -/
def BeginReturns {World Ghost : Type} (code : UInt64) (rep : Ghost → World → Prop)
    (Inv : State → Ghost → Prop) (next : ProcessStep State) (ghost : Ghost) (final : World) :
    Prop :=
  rep ghost final ∧ Safe next.state ∧ (next.running = false → next.status = code) ∧
    (next.running = true → Inv next.state ghost)

theorem Compiled.control_begin_replies {start : Action (ProcessStep State)} (c : Compiled start)
    {World Ghost : Type} {host : Host World} {code : UInt64}
    {rep : Ghost → World → Prop} {Inv : State → Ghost → Prop} {world : World}
    {Room : ProcessStep State → Prop}
    (begins : ∀ {trace outcome final}, LeanExe.Wasi.Exec host start world trace outcome final →
      ∃ next ghost, outcome = .returned next ∧ BeginReturns code rep Inv next ghost final ∧
        Room next)
    {trace outcome final}
    (execution : LeanExe.Wasi.Exec host (c.entry.beginAction (c.program.funs c.pure.funs))
      world trace outcome final) :
    ∃ next ghost current, outcome = .returned current ∧
      ControlRep code rep Inv (next, ghost) current final ∧ Room next := by
  obtain ⟨nativeOutcome, nativeExecution, related⟩ := c.beginRelated.exec_back execution
  obtain ⟨next, ghost, same, ⟨ready, safe, stopped, running⟩, room⟩ :=
    begins nativeExecution
  subst same
  cases related with
  | returned related =>
      exact ⟨next, ghost, _, rfl, ⟨related, safe, ready, stopped, running⟩, room⟩

/-- A step from a represented running state returns a represented state of lower rank, and the
native step from the ghost's state returns the ghost's next state. -/
theorem Compiled.control_step_replies {start : Action (ProcessStep State)} (c : Compiled start)
    {World Ghost : Type} {host : Host World} {code : UInt64}
    {rep : Ghost → World → Prop} {unread zeroWrites : Ghost → Nat}
    {Inv : State → Ghost → Prop}
    (progress : StreamProgress host rep unread zeroWrites)
    (advances : StepAdvances host rep zeroWrites Inv) (stops : code = 0)
    {ghost : ControlGhost Ghost} {current : ProcessStep stateTy.denote}
    {world : World} (held : ControlRep code rep Inv ghost current world)
    (running : current.running = true)
    {trace outcome final}
    (execution : LeanExe.Wasi.Exec host (c.entry.action (c.program.funs c.pure.funs) current.state)
      world trace outcome final) :
    ∃ nextGhost next, outcome = .returned next ∧
      ControlRep code rep Inv nextGhost next final ∧
      ControlLt zeroWrites nextGhost ghost ∧
      LeanExe.Wasi.Exec host (step ghost.1.state) world trace (.returned nextGhost.1) final := by
  obtain ⟨related, safe, ready, _, invariant⟩ := held
  have beforeRunning : ghost.1.running = true := related.running.trans running
  obtain ⟨nativeOutcome, nativeExecution, resultRelated⟩ :=
    (c.stepRelated ghost.1.state current.state related.state).exec_back execution
  obtain ⟨nativeNext, same⟩ := step_returned progress ready safe nativeExecution
  cases same
  cases resultRelated with
  | returned nextRelated =>
      obtain ⟨_, _, nextSafe, status, _⟩ := step_advances progress ready safe nativeExecution
      obtain ⟨nextGhost, nextRep, after⟩ :=
        advances safe (invariant beforeRunning) ready nativeExecution
      refine ⟨(nativeNext, nextGhost), _, rfl,
        ⟨nextRelated, nextSafe, nextRep, fun stopped => (status stopped).trans stops.symm,
          fun nextRunning => (after nextRunning).1⟩, ?_, nativeExecution⟩
      change controlOrder.rel (controlRank zeroWrites (nativeNext, nextGhost))
        (controlRank zeroWrites ghost)
      cases afterRunning : nativeNext.running with
      | false =>
          simp only [controlRank, afterRunning, beforeRunning, ↓reduceIte]
          exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)
      | true =>
          simp only [controlRank, afterRunning, beforeRunning, ↓reduceIte]
          exact Prod.Lex.right _ (after afterRunning).2

theorem control_exit_accepted {World Ghost : Type} {host : Host World} {code : UInt64}
    {rep : Ghost → Observed World → Prop} {Inv : State → Ghost → Prop}
    (accepted : ∀ ghost world, rep ghost world → ∀ message final,
      (observedHost host).exitTrap world (exitStatus code) message final → False)
    {ghost : ControlGhost Ghost} {current : ProcessStep stateTy.denote}
    {world : Observed World} (held : ControlRep code rep Inv ghost current world)
    (stopped : current.running = false) {message final}
    (rejected : (observedHost host).exitTrap world (exitStatus current.status) message final) :
    False := by
  obtain ⟨related, _, ready, status, _⟩ := held
  have nativeStopped := related.running.trans stopped
  have same : current.status = code := by rw [← related.status]; exact status nativeStopped
  rw [same] at rejected
  exact accepted ghost.2 world ready message final rejected

def TargetTerminated {World : Type} (host : Host World) (code : UInt64) :
    Result (Observed World) → Prop
  | .Trap final message => message = exitTrap ∧
      ∃ before, (observedHost host).exit before (exitStatus code) final.host
  | _ => False

/-- The compiled process exits with the accepted status `code` when the host makes progress,
every run of the native `start` returns a state that stops with `code` or runs under the
invariant `Inv`, which each step keeps, a step that stops returns `code`, `begin` and every
reached step have prefix bounds `beginCharge` and `charge`, and the room conditions hold for them
and the copies of the states.  The conditions on a step need hold only at states where `Inv` holds
with the ghost. -/
theorem Compiled.target_terminates {start : Action (ProcessStep State)} (c : Compiled start)
    {World Ghost : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : Ghost → Observed World → Prop) (unread zeroWrites : Ghost → Nat)
    (progress : StreamProgress (observedHost host) rep unread zeroWrites)
    (Inv : State → Ghost → Prop) (code : UInt64)
    (advances : StepAdvances (observedHost host) rep zeroWrites Inv)
    (stops : (∃ s ghost, Inv s ghost) → code = 0)
    (valid : targetHost.Satisfies c.module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : c.pool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap c.module 0 ≤ 65535)
    (charge : ProcessStep State → Ghost → Nat) (beginCharge : Nat)
    (beginRoom : heap.top.toNat + beginCharge ≤
      65536 * (PureTransport.erase initial).memoryCap c.source 0)
    (beginBounded : Resource.CallPrefixBound (observedHost host) c.pure c.program c.entry.begin 0
      .nil initial.host beginCharge)
    (begins : ∀ {trace outcome final},
      LeanExe.Wasi.Exec (observedHost host) start initial.host trace outcome final →
      ∃ next ghost, outcome = .returned next ∧ BeginReturns code rep Inv next ghost final ∧
        heap.top.toNat + beginCharge + stateTy.copyCost (sourceState next.state) ≤
          65536 * (PureTransport.erase initial).memoryCap c.source 0)
    (stepBounded : ∀ (native : ProcessStep State) ghost (world : Observed World),
      Safe native.state → rep ghost world → native.running = true → Inv native.state ghost →
      heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native ghost ≤
          65536 * (PureTransport.erase initial).memoryCap c.source 0 ∧
        Resource.CallPrefixBound (observedHost host) c.pure c.program c.entry.step 0
          (.cons (sourceState native.state) .nil) world (charge native ghost))
    (stepRoom : ∀ (native : ProcessStep State) ghost (world : Observed World),
      Safe native.state → rep ghost world → native.running = true → Inv native.state ghost →
      ∀ trace next final nextGhost,
      LeanExe.Wasi.Exec (observedHost host) (step native.state) world trace (.returned next)
        final →
      rep nextGhost final →
      heap.top.toNat + stateTy.copyCost (sourceState native.state) + charge native ghost +
          stateTy.copyCost (sourceState next.state) ≤
        65536 * (PureTransport.erase initial).memoryCap c.source 0)
    (accepted : ∀ ghost world, rep ghost world → ∀ message final,
      (observedHost host).exitTrap world (exitStatus code) message final → False) :
    ∃ bound, ∀ fuel ≥ bound,
      TargetTerminated host code (run fuel c.module c.startIndex initial [] targetHost) ∧
      ProcessEntryRunResult (observedHost host) start process initial.host
        (run fuel c.module c.startIndex initial [] targetHost) := by
  obtain ⟨bound, allFuel⟩ := compiled_process_total_run c.program c.entry c.pool c.calls
    c.runtime c.profile compactable compactForm c.compactClosed (ControlRep code rep Inv)
    (ControlLt zeroWrites)
    (control_wellFounded zeroWrites) (fun ghost _ => charge ghost.1 ghost.2) beginCharge
    valid at_ free static c.poolScratch cap
    { beginRoom := beginRoom
      beginBounded := beginBounded
      beginReplies := fun _ _ _ execution => by
        obtain ⟨next, ghost, current, same, held, room⟩ :=
          c.control_begin_replies (Room := fun next =>
            heap.top.toNat + beginCharge + stateTy.copyCost (sourceState next.state) ≤
              65536 * (PureTransport.erase initial).memoryCap c.source 0)
            begins execution
        refine ⟨(next, ghost), current, same, held, ?_⟩
        rw [held.1.state]
        exact room
      stepRoom := fun ghost current world held running => by
        obtain ⟨related, safe, ready, _, invariant⟩ := held
        have nativeRunning := related.running.trans running
        rw [related.state]
        exact (stepBounded ghost.1 ghost.2 world safe ready nativeRunning
          (invariant nativeRunning)).1
      stepBounded := fun ghost current world held running => by
        obtain ⟨related, safe, ready, _, invariant⟩ := held
        have nativeRunning := related.running.trans running
        rw [related.state]
        exact (stepBounded ghost.1 ghost.2 world safe ready nativeRunning
          (invariant nativeRunning)).2
      stepReplies := fun ghost current world held running trace outcome final execution => by
        have stopsZero : code = 0 := by
          obtain ⟨related, _, _, _, invariant⟩ := held
          exact stops ⟨_, _, invariant (related.running.trans running)⟩
        obtain ⟨nextGhost, next, same, nextHeld, smaller, nativeExecution⟩ :=
          c.control_step_replies progress advances stopsZero held running execution
        refine ⟨nextGhost, next, same, nextHeld, smaller, ?_⟩
        obtain ⟨related, safe, ready, _, invariant⟩ := held
        have nativeRunning := related.running.trans running
        rw [related.state, nextHeld.1.state]
        exact stepRoom ghost.1 ghost.2 world safe ready nativeRunning (invariant nativeRunning)
          trace nextGhost.1 final nextGhost.2 nativeExecution nextHeld.2.2.1 }
    (fun _ _ _ held stopped _ _ rejected => control_exit_accepted accepted held stopped rejected)
  refine ⟨bound, fun fuel enough => ?_⟩
  have total : ProcessTotalRunExited host stateTy (ControlRep code rep Inv)
      (run fuel c.module c.startIndex initial [] targetHost) := allFuel fuel enough
  have completed : run fuel c.module c.startIndex initial [] targetHost ≠ .OutOfFuel := by
    intro same
    rw [same] at total
    exact total
  refine ⟨?_, c.implements host targetHost initial heap fuel valid at_ free static cap completed⟩
  generalize execution : run fuel c.module c.startIndex initial [] targetHost = result at total ⊢
  cases result with
  | Trap final message =>
      obtain ⟨messageEq, ghost, current, before, held, stopped, exited⟩ := total
      obtain ⟨related, _, _, status, _⟩ := held
      have same : current.status = code := by
        rw [← related.status]
        exact status (related.running.trans stopped)
      exact ⟨messageEq, before, by rw [← same]; exact exited⟩
  | _ => exact total.elim

/-! ## Commands -/

/-- The host accepts the exit status `code` at every represented world. -/
def ExitAccepted {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) (code : UInt64) : Prop :=
  ∀ position world, observedStreamRep rep position world → ∀ message final,
    (observedHost host).exitTrap world (exitStatus code) message final → False

/-- A step from a state with the invariant keeps it, at a lower rank while the process runs, with
one next stream position for both. -/
theorem future_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {expected : List UInt64} {maxOutput : Nat}
    {s : State} {position : StreamPosition}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Writes expected maxOutput s position)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → Writes expected maxOutput next.state nextPosition ∧
        RankLt (rank StreamPosition.zeroWrites next.state nextPosition)
          (rank StreamPosition.zeroWrites s position)) := by
  by_cases pending : s.written < s.output.size
  · rw [step_write pending] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput s) fun reply => .pure (afterWrite s reply))
      world trace (.returned next) final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        obtain ⟨count, nextPosition, replyEq, nextRep, sameInput, output, zeroDrop⟩ :=
          streams.write_reply represented (remainingOutput_nonempty future.safe pending) operation
        cases replyEq
        simp only [writeResult, ↓reduceIte]
        have bound := (host.write_bound operation).1
        exact ⟨nextPosition, nextRep, fun _ =>
          ⟨future_afterWrite future _ bound sameInput output,
            rank_afterWrite _ future.safe pending _ bound zeroDrop⟩⟩
  · rw [step_stop pending] at execution
    cases execution
    exact ⟨position, represented, fun impossible => by cases impossible⟩

theorem charge_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {expected : List UInt64} {maxOutput : Nat} :
    StepAdvances (observedHost host) (observedStreamRep rep) StreamPosition.zeroWrites
      (Writes expected maxOutput) := by
  intro s position world final trace next _ future represented execution
  obtain ⟨nextPosition, nextRep, after⟩ :=
    future_advances streams.observed represented future execution
  exact ⟨nextPosition, nextRep, fun running => after running⟩

def CommandResult {World : Type} (host : Host World) (rep : StreamPosition → World → Prop)
    (code : UInt64) (output : List UInt64) (outcome : Outcome Unit) (final : Observed World) :
    Prop :=
  stdoutWords final.events = output ∧
    ∃ before position, observedStreamRep rep position before ∧ position.output = output ∧
      ((outcome = .exited (exitStatus code) ∧ (observedHost host).exit before (exitStatus code)
          final) ∨
        ∃ message, outcome = .trapped message ∧
          (observedHost host).exitTrap before (exitStatus code) message final)

theorem finished_result {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} {position : StreamPosition} {code : UInt64}
    {output : List UInt64} {before final : Observed World} {last : List Event}
    {result : Outcome Unit} (represented : observedStreamRep rep position before)
    (written : position.output = output)
    (finished : LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) code) before last
      result final) :
    CommandResult host rep code output result final := by
  cases finished with
  | exit accepted =>
      have finalOutput := StreamFold.observedStreamRep_exit_output represented accepted
      exact ⟨finalOutput.symm.trans written, _, position, represented, written,
        Or.inl ⟨rfl, accepted⟩⟩
  | exitTrap rejected =>
      have finalOutput := StreamFold.observedStreamRep_exitTrap_output represented rejected
      exact ⟨finalOutput.symm.trans written, _, position, represented, written,
        Or.inr ⟨_, rfl, rejected⟩⟩

/-- Every terminal execution of `beginWith tab` and the process followed by the exit of its
status, on an input of at most `limit` bytes, writes the bytes of `expected` of the input and exits
with status 0, or ends in a rejected exit of it. -/
theorem command_output {tab : LeanExe.Bytes → LeanExe.Bytes} {expected : List UInt64 → List UInt64}
    {maxOutput : Nat}
    (report : ∀ (b : LeanExe.Bytes), b.data.size < 2 ^ 32 → ∀ {position : StreamPosition},
      position.input = [] → position.output = [] →
      Writes (expected (byteWords b)) maxOutput ⟨tab b, 0⟩ position)
    {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : position.input.length ≤ limit.toNat)
    (execution : ProcessCommandExec (observedHost host) (beginWith tab) process world trace
      outcome final) :
    CommandResult host rep 0 (expected position.input) outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      obtain ⟨first, firstPosition, same, firstRep, running, _, future⟩ :=
        beginWith_report report streams.observed size empty observed started
      cases same
      simp only [Process.Continue, running, ↓reduceIte] at continued
      obtain ⟨nextPosition, nextRep, returned, output, _⟩ :=
        process_exec_correct streams.observed continued firstRep future
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) 0) _ _ _ _ at finished
      exact finished_result nextRep output finished
  | beginExit execution =>
      obtain ⟨_, _, impossible, _⟩ :=
        beginWith_report report streams.observed size empty observed execution
      cases impossible
  | beginTrap execution =>
      obtain ⟨_, _, impossible, _⟩ :=
        beginWith_report report streams.observed size empty observed execution
      cases impossible

/-- Every terminal execution of `beginWith tab` and the process followed by the exit of its
status, on an input of more than `limit` bytes, writes nothing and exits with status `tooLong`, or
ends in a rejected exit of it. -/
theorem command_output_long {tab : LeanExe.Bytes → LeanExe.Bytes} {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : limit.toNat < position.input.length)
    (execution : ProcessCommandExec (observedHost host) (beginWith tab) process world trace
      outcome final) :
    CommandResult host rep tooLong [] outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      obtain ⟨nextPosition, same, nextRep, output⟩ :=
        beginWith_long streams.observed size observed started
      cases same
      simp only [Process.Continue, Bool.false_eq_true, ↓reduceIte] at continued
      obtain ⟨rfl, rfl, rfl⟩ := continued
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) tooLong) _ _ _ _
        at finished
      exact finished_result nextRep (output.trans empty) finished
  | beginExit execution =>
      obtain ⟨_, impossible, _⟩ := beginWith_long streams.observed size observed execution
      cases impossible
  | beginTrap execution =>
      obtain ⟨_, impossible, _⟩ := beginWith_long streams.observed size observed execution
      cases impossible

/-- A run that ends in the exit trap with status `code`, whose native run under the begin action
`start` and the process gives `CommandResult` for every terminal execution, writes `output` and
records the exit status `code`. -/
theorem result_output {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    {start : Action (ProcessStep State)}
    {code : UInt64} {output : List UInt64} {world : Observed World}
    (accepted : ExitAccepted host rep code) {final : Store (Observed World)} {message : String}
    (total : TargetTerminated host code (.Trap final message))
    (native : ProcessEntryRunResult (observedHost host) start process world (.Trap final message))
    (commands : ∀ {trace outcome final}, ProcessCommandExec (observedHost host) start process
      world trace outcome final → CommandResult host rep code output outcome final) :
    stdoutWords final.host.events = output ∧
      host.exited final.host.world = some (exitStatus code) := by
  change ProcessEntryResult (observedHost host) start process world (.Trap final message) at native
  cases native with
  | terminal final trace outcome message execution terminal =>
      obtain ⟨written, before, nextPosition, nextRep, _, finished⟩ := commands execution
      rcases finished with ⟨returned, operation⟩ | ⟨error, trapped, operation⟩
      · exact ⟨written, host.exit_recorded operation.1⟩
      · exact False.elim (accepted nextPosition before nextRep error _ operation)
  | resource final trace residual progress =>
      have impossible : ("unreachable" : String) = exitTrap := total.1
      exact False.elim ((by decide : ("unreachable" : String) ≠ exitTrap) impossible)

/-! ## Runs from a store with room -/

/-- For a process whose `start` is `beginWith tab`, from a store with an allocator at `heap`, the
literal pool, and room above `heap.top` for `beginCharge` and `copyLimit` bytes, the module's
`_start` exits with status 0 after writing exactly the bytes of `expected` of an input of at most
`limit` bytes.  `report` states the invariant `Writes` of the state of `tab b`, `copy` bounds the
copy of a state of at most `maxOutput` bytes of output by `copyLimit`, and `beginBound` and
`stepBound` are the prefix bounds of `begin` and of a step from such a state. -/
theorem Compiled.terminates_of_room {tab : LeanExe.Bytes → LeanExe.Bytes}
    (c : Compiled (beginWith tab))
    {expected : List UInt64 → List UInt64} {maxOutput copyLimit beginCharge : Nat}
    (report : ∀ (b : LeanExe.Bytes), b.data.size < 2 ^ 32 → ∀ {position : StreamPosition},
      position.input = [] → position.output = [] →
      Writes (expected (byteWords b)) maxOutput ⟨tab b, 0⟩ position)
    (copy : ∀ s : State, s.output.data.size ≤ maxOutput →
      stateTy.copyCost (sourceState s) ≤ copyLimit)
    (chargeLe : 3 * copyLimit ≤ beginCharge)
    (beginBound : ∀ {World : Type} (host : Host World) (world : World),
      Resource.CallPrefixBound host c.pure c.program c.entry.begin 0 .nil world beginCharge)
    (stepBound : ∀ {World : Type} (host : Host World) (s : State),
      s.output.data.size ≤ maxOutput → ∀ world : World,
      Resource.CallPrefixBound host c.pure c.program c.entry.step 0 (.cons (sourceState s) .nil)
        world (2 * copyLimit))
    {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (size : position.input.length ≤ limit.toNat)
    (valid : targetHost.Satisfies c.module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : c.pool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap c.module 0 ≤ 65535)
    (room : heap.top.toNat + (beginCharge + copyLimit) ≤
      65536 * (PureTransport.erase initial).memoryCap c.source 0)
    (accepted : ExitAccepted host rep 0) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel c.module c.startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expected position.input ∧
        host.exited final.host.world = some 0 := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  obtain ⟨bound, executions⟩ := c.target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress (Writes (expected position.input) maxOutput) 0
    (charge_advances streams) (fun _ => rfl) valid at_ free static cap
    (fun _ _ => 2 * copyLimit) beginCharge (by omega) (beginBound (observedHost host) initial.host)
    (fun execution => by
      obtain ⟨first, firstPosition, same, firstRep, running, _, future⟩ :=
        beginWith_report report streams.observed size empty observed execution
      have copied := copy _ future.outputSize
      exact ⟨first, firstPosition, same,
        ⟨firstRep, future.safe, (fun stopped => by rw [running] at stopped; cases stopped),
          fun _ => future⟩, by omega⟩)
    (fun native ghost world _ represented _ future => by
      have copied := copy _ future.outputSize
      refine ⟨?_, stepBound (observedHost host) native.state future.outputSize world⟩
      show heap.top.toNat + stateTy.copyCost (sourceState native.state) + 2 * copyLimit ≤ _
      omega)
    (fun native ghost world _ represented _ future _ next final _ execution _ => by
      have copied := copy _ future.outputSize
      have nextCopy := copy _ (step_output_le streams.observed represented future execution)
      show heap.top.toNat + stateTy.copyCost (sourceState native.state) + 2 * copyLimit +
        stateTy.copyCost (sourceState next.state) ≤ _
      omega)
    accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed :
    run fuel c.module c.startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      have written := result_output (output := expected position.input) accepted total
        native (fun execution =>
          command_output report streams represented events empty size execution)
      rw [show exitStatus 0 = 0 by decide] at written
      exact ⟨final, by simp [messageEq], written.1, written.2⟩
  | _ => exact total.elim

/-- For a process whose `start` is `beginWith tab`, from a store with an allocator at `heap`, the
literal pool, and room above `heap.top` for `beginCharge` bytes, the module's `_start` exits with
status `tooLong` after writing nothing, for an input of more than `limit` bytes. -/
theorem Compiled.exits_long_of_room {tab : LeanExe.Bytes → LeanExe.Bytes}
    (c : Compiled (beginWith tab))
    {beginCharge : Nat}
    (beginBound : ∀ {World : Type} (host : Host World) (world : World),
      Resource.CallPrefixBound host c.pure c.program c.entry.begin 0 .nil world beginCharge)
    {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (size : limit.toNat < position.input.length)
    (valid : targetHost.Satisfies c.module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : c.pool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap c.module 0 ≤ 65535)
    (room : heap.top.toNat + beginCharge ≤
      65536 * (PureTransport.erase initial).memoryCap c.source 0)
    (accepted : ExitAccepted host rep tooLong) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel c.module c.startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = [] ∧ host.exited final.host.world = some tooLong := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  obtain ⟨bound, executions⟩ := c.target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress (fun _ _ => False) tooLong
    (fun _ impossible => False.elim impossible)
    (fun ⟨_, _, impossible⟩ => False.elim impossible)
    valid at_ free static cap (fun _ _ => 0) beginCharge
    room (beginBound (observedHost host) initial.host)
    (fun execution => by
      obtain ⟨nextPosition, same, nextRep, _⟩ :=
        beginWith_long streams.observed size observed execution
      have copied : stateTy.copyCost (sourceState Demos.Rcv.Process.initial) = 0 := by decide
      exact ⟨_, nextPosition, same,
        ⟨nextRep, Safe.initial, fun _ => rfl, fun impossible => by cases impossible⟩,
        by
          show _ + _ + stateTy.copyCost (sourceState Demos.Rcv.Process.initial) ≤ _
          rw [copied]
          omega⟩)
    (fun _ _ _ _ _ _ impossible => False.elim impossible)
    (fun _ _ _ _ _ _ impossible => False.elim impossible)
    accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed :
    run fuel c.module c.startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      have written := result_output (output := []) accepted total native (fun execution =>
          command_output_long streams represented events empty size execution)
      rw [show exitStatus tooLong = tooLong by decide] at written
      exact ⟨final, by simp [messageEq], written.1, written.2⟩
  | _ => exact total.elim

end Demos.Rcv.Process
