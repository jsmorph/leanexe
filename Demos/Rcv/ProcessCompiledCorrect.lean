import Demos.Rcv.ProcessCharges
import Demos.Rcv.ProcessCorrect
import Demos.Rcv.ProcessTermination
import Demos.StreamFold.Observed
import Verified.Wasi.ProcessEntryProofs

/-! The correctness of the compiled process.  Under StreamFold's host assumptions, a Talos host
that satisfies the three import specifications, and a host that accepts the exit status,
`initial_terminates` states that the module's `_start`, from its initial store, exits with status 0
after writing exactly the bytes of the report of an input of at most `limit` bytes, and
`initial_exits_long` that it exits with status `tooLong` after writing nothing for a longer input.
The memory of a run is a closed number: the buffer of `readAll`, the call of `tabulate` on at most
`limit` bytes, and the copy of a state fit in the 65,535 pages above the literal pool, as
`processMemory_le` states, so neither theorem has a memory premise. -/

namespace Demos.Rcv.Process

open Wasm _root_.Verified _root_.Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

/-- The host accepts the exit status `code` at every represented world. -/
def ExitAccepted {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) (code : UInt64) : Prop :=
  ∀ position world, observedStreamRep rep position world → ∀ message final,
    (observedHost host).exitTrap world (exitStatus code) message final → False

/-- A step from a state with the invariant keeps it, at a lower rank while the process runs, with
one next stream position for both. -/
theorem future_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
    {s : State} {position : StreamPosition}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → Future input next.state nextPosition ∧
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
    (streams : StreamHost host rep) {input : List UInt64} :
    StepAdvances (observedHost host) (observedStreamRep rep) StreamPosition.zeroWrites
      (Future input) := by
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

/-- Every terminal execution of `begin` and the process followed by the exit of its status, on an
input of at most `limit` bytes, writes the bytes of `expectedOutput` and exits with status 0, or
ends in a rejected exit of it. -/
theorem command_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : position.input.length ≤ limit.toNat)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandResult host rep 0 (expectedOutput position.input) outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      obtain ⟨first, firstPosition, same, firstRep, running, _, future⟩ :=
        begin_report streams.observed size empty observed started
      cases same
      simp only [Process.Continue, running, ↓reduceIte] at continued
      obtain ⟨nextPosition, nextRep, returned, output, _⟩ :=
        process_exec_correct streams.observed continued firstRep future
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) 0) _ _ _ _ at finished
      exact finished_result nextRep output finished
  | beginExit execution =>
      obtain ⟨_, _, impossible, _⟩ :=
        begin_report streams.observed size empty observed execution
      cases impossible
  | beginTrap execution =>
      obtain ⟨_, _, impossible, _⟩ :=
        begin_report streams.observed size empty observed execution
      cases impossible

/-- Every terminal execution of `begin` and the process followed by the exit of its status, on an
input of more than `limit` bytes, writes nothing and exits with status `tooLong`, or ends in a
rejected exit of it. -/
theorem command_output_long {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : limit.toNat < position.input.length)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandResult host rep tooLong [] outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      obtain ⟨nextPosition, same, nextRep, output⟩ :=
        begin_long streams.observed size observed started
      cases same
      simp only [Process.Continue, Bool.false_eq_true, ↓reduceIte] at continued
      obtain ⟨rfl, rfl, rfl⟩ := continued
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) tooLong) _ _ _ _
        at finished
      exact finished_result nextRep (output.trans empty) finished
  | beginExit execution =>
      obtain ⟨_, impossible, _⟩ := begin_long streams.observed size observed execution
      cases impossible
  | beginTrap execution =>
      obtain ⟨_, impossible, _⟩ := begin_long streams.observed size observed execution
      cases impossible

theorem result_output {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    {code : UInt64} {output : List UInt64} {world : Observed World}
    (accepted : ExitAccepted host rep code) {final : Store (Observed World)} {message : String}
    (total : TargetTerminated host code (.Trap final message))
    (native : ProcessEntryRunResult (observedHost host) begin process world (.Trap final message))
    (commands : ∀ {trace outcome final}, ProcessCommandExec (observedHost host) begin process
      world trace outcome final → CommandResult host rep code output outcome final) :
    stdoutWords final.host.events = output ∧
      host.exited final.host.world = some (exitStatus code) := by
  change ProcessEntryResult (observedHost host) begin process world (.Trap final message) at native
  cases native with
  | terminal final trace outcome message execution terminal =>
      obtain ⟨written, before, nextPosition, nextRep, _, finished⟩ := commands execution
      rcases finished with ⟨returned, operation⟩ | ⟨error, trapped, operation⟩
      · exact ⟨written, host.exit_recorded operation.1⟩
      · exact False.elim (accepted nextPosition before nextRep error _ operation)
  | resource final trace residual progress =>
      have impossible : ("unreachable" : String) = exitTrap := total.1
      exact False.elim ((by decide : ("unreachable" : String) ≠ exitTrap) impossible)

theorem memoryCap_pure {α : Type} (store : Store α) :
    store.memoryCap module 0 = store.memoryCap io.pure.module 0 :=
  PureTransport.memoryCap_zero_eq rfl store

/-- The bytes above the literal pool that a run needs: the charge of `begin` and the copy of a
state, which bound the charges of the steps as well. -/
def processMemory : Nat := beginCharge + copyLimit

theorem processMemory_eq : processMemory = 4085008138 := by
  rw [processMemory, beginCharge_eq]
  rfl

/-- From a store with an allocator at `heap`, the literal pool, and room above `heap.top` for
`processMemory` bytes, the module's `_start` exits with status 0 after writing exactly the bytes of
the report of an input of at most `limit` bytes. -/
theorem terminates_of_room {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (size : position.input.length ≤ limit.toNat)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (room : heap.top.toNat + processMemory ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep 0) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  have chargeLe : 3 * copyLimit ≤ beginCharge := by rw [beginCharge_eq]; decide
  unfold processMemory at room
  obtain ⟨bound, executions⟩ := target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress (Future position.input) 0 (charge_advances streams)
    (fun _ => rfl) valid at_ free static cap (fun _ _ => stepCharge) beginCharge
    (by omega) (begin_prefix_bound (observedHost host) initial.host)
    (fun execution => by
      obtain ⟨first, firstPosition, same, firstRep, running, _, future⟩ :=
        begin_report streams.observed size empty observed execution
      have copy := future.sized.copyCost
      exact ⟨first, firstPosition, same,
        ⟨firstRep, future.safe, (fun stopped => by rw [running] at stopped; cases stopped),
          fun _ => future⟩, by omega⟩)
    (fun native ghost world _ represented _ future => by
      have copy := future.sized.copyCost
      refine ⟨?_, step_prefix_bound (observedHost host) future.sized world⟩
      show heap.top.toNat + stateTy.copyCost (sourceState native.state) + stepCharge ≤ _
      unfold stepCharge
      omega)
    (fun native ghost world _ represented _ future _ next final _ execution _ => by
      have copy := future.sized.copyCost
      have nextCopy := (step_sized streams.observed represented future execution).copyCost
      show heap.top.toNat + stateTy.copyCost (sourceState native.state) + stepCharge +
        stateTy.copyCost (sourceState next.state) ≤ _
      unfold stepCharge
      omega)
    accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed :
    run fuel module startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      have written := result_output (output := expectedOutput position.input) accepted total
        native (fun execution =>
          command_output streams represented events empty size execution)
      rw [show exitStatus 0 = 0 by decide] at written
      exact ⟨final, by simp [messageEq], written.1, written.2⟩
  | _ => exact total.elim

/-- From a store with an allocator at `heap`, the literal pool, and room above `heap.top` for the
charge of `begin`, the module's `_start` exits with status `tooLong` after writing nothing, for an
input of more than `limit` bytes. -/
theorem exits_long_of_room {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (size : limit.toNat < position.input.length)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (room : heap.top.toNat + processMemory ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep tooLong) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = [] ∧ host.exited final.host.world = some tooLong := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  unfold processMemory at room
  obtain ⟨bound, executions⟩ := target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress (fun _ _ => False) tooLong
    (fun _ impossible => False.elim impossible)
    (fun ⟨_, _, impossible⟩ => False.elim impossible)
    valid at_ free static cap (fun _ _ => 0) beginCharge
    (by omega) (begin_prefix_bound (observedHost host) initial.host)
    (fun execution => by
      obtain ⟨nextPosition, same, nextRep, _⟩ :=
        begin_long streams.observed size observed execution
      have copy : stateTy.copyCost (sourceState Demos.Rcv.Process.initial) = 0 := by decide
      exact ⟨_, nextPosition, same,
        ⟨nextRep, Safe.initial, fun _ => rfl, fun impossible => by cases impossible⟩,
        by
          show _ + _ + stateTy.copyCost (sourceState Demos.Rcv.Process.initial) ≤ _
          rw [copy]
          omega⟩)
    (fun _ _ _ _ _ _ impossible => False.elim impossible)
    (fun _ _ _ _ _ _ impossible => False.elim impossible)
    accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed :
    run fuel module startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      have written := result_output (output := []) accepted total native (fun execution =>
          command_output_long streams represented events empty size execution)
      rw [show exitStatus tooLong = tooLong by decide] at written
      exact ⟨final, by simp [messageEq], written.1, written.2⟩
  | _ => exact total.elim

set_option maxHeartbeats 2000000 in
theorem initial_memoryCap {World : Type} (world : Observed World) :
    (PureTransport.erase (initialStore world)).memoryCap io.pure.module 0 = 65535 := by
  rw [initialStore, PureTransport.erase_restore]
  decide +kernel

theorem initial_top : (initialStaticHeap io.literalPool).top.toNat = 4096 := by
  decide +kernel

/-- The memory of a run fits above the literal pool, which ends at 4,096 bytes, in the 65,535
pages of the module's memory. -/
theorem processMemory_le : 4096 + processMemory ≤ 65536 * 65535 := by
  rw [processMemory_eq]
  decide

/-- For every input of at most 50,000,000 bytes, under StreamFold's host assumptions, a Talos host
that satisfies the import specifications, and a host that accepts the exit status 0, the compiled
command from its initial store exits with status 0 after writing exactly the bytes of the report
of the input. -/
theorem initial_terminates {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : position.input.length ≤ 50000000)
    (valid : targetHost.Satisfies module (hostSpec host)) (accepted : ExitAccepted host rep 0) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 :=
  terminates_of_room host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty (by rw [limit_toNat]; exact size) valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1
    (by rw [initial_top, initial_memoryCap]; exact processMemory_le) accepted

/-- For every input of more than 50,000,000 bytes, under StreamFold's host assumptions, a Talos
host that satisfies the import specifications, and a host that accepts the exit status
`tooLong`, the compiled command from its initial store exits with status `tooLong`, 22, after
writing nothing. -/
theorem initial_exits_long {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : 50000000 < position.input.length)
    (valid : targetHost.Satisfies module (hostSpec host))
    (accepted : ExitAccepted host rep tooLong) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = [] ∧ host.exited final.host.world = some tooLong :=
  exits_long_of_room host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty (by rw [limit_toNat]; exact size) valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1
    (by rw [initial_top, initial_memoryCap]; exact processMemory_le) accepted

/-- One byte sequence encodes the module, decodes to it, and is a valid binary, and the module
satisfies `initial_terminates` and `initial_exits_long`. -/
theorem terminates_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates) ∧
      (type_of% @initial_exits_long) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates, @initial_exits_long⟩

end Demos.Rcv.Process
