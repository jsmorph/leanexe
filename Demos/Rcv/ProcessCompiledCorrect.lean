import Demos.Rcv.ProcessCharges
import Demos.Rcv.ProcessCorrect
import Demos.Rcv.ProcessTermination
import Demos.StreamFold.Observed
import Verified.Wasi.ProcessEntryProofs

/-! The correctness of the compiled process.  Under StreamFold's host assumptions, a Talos host
that satisfies the three import specifications, a host that accepts the exit status 0, and an input
of at most `L` bytes, `initial_terminates` states that the module's `_start` exits with status 0
after writing exactly the bytes of the report of the input, when `processMemory L` bytes fit in its
memory of 65,535 pages above the literal pool.  `processMemory L` is room for two copies of a state
and a step's charge, of which the largest is the call of `tabulate` on the whole input, with the
closed form `TabulateProgram.tabulate_bound` of its bound.  `initial_terminates_50000000` fixes `L`
at 50,000,000 bytes. -/

namespace Demos.Rcv.Process

open Wasm _root_.Verified _root_.Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

/-- The host accepts the exit status 0 at every represented world. -/
def ExitAccepted {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) : Prop :=
  ∀ position world, observedStreamRep rep position world → ∀ status,
    status = 0 → ∀ message final,
    (observedHost host).exitTrap world (exitStatus status) message final → False

/-- A step from a state with the invariant keeps it, at a lower rank while the process runs, with
one next stream position for both. -/
theorem future_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {position : StreamPosition}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → Future input next.state nextPosition ∧
        RankLt (rank (fun p : StreamPosition => p.input.length) StreamPosition.zeroWrites
            next.state nextPosition)
          (rank (fun p : StreamPosition => p.input.length) StreamPosition.zeroWrites s
            position)) := by
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
          ⟨future_afterWrite future pending _ bound sameInput output,
            rank_afterWrite _ _ future.safe pending _ bound (congrArg List.length sameInput)
              zeroDrop⟩⟩
  · cases eof : s.eof with
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        exact ⟨position, represented, fun impossible => by cases impossible⟩
    | false =>
        rw [step_read pending eof] at execution
        change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead s reply))
          world trace (.returned next) final at execution
        cases execution with
        | read_reject capacity continuation =>
            exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
        | read_return capacity operation continuation =>
            cases continuation
            obtain ⟨bytes, nextPosition, replyEq, nextRep, consumed, atEof, sameOutput⟩ :=
              streams.read_reply represented operation
            cases replyEq
            simp only [readResult, ↓reduceIte]
            have length := congrArg List.length consumed
            simp only [List.length_append, Demos.StreamFold.byteWords_length] at length
            exact ⟨nextPosition, nextRep, fun _ =>
              ⟨future_readStep short future eof consumed atEof sameOutput,
                rank_afterRead _ _ eof (by omega) (fun _ => by omega)⟩⟩

theorem charge_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64} (short : input.length < 2 ^ 32) :
    StepAdvances (observedHost host) (observedStreamRep rep) (fun position => position.input.length)
      StreamPosition.zeroWrites (Future input) := by
  intro s position world final trace next _ future represented execution
  obtain ⟨nextPosition, nextRep, after⟩ :=
    future_advances streams.observed short represented future execution
  exact ⟨nextPosition, nextRep, fun running => after running⟩

def CommandResult {World : Type} (host : Host World) (rep : StreamPosition → World → Prop)
    (input : List UInt64) (outcome : Outcome Unit) (final : Observed World) : Prop :=
  stdoutWords final.events = expectedOutput input ∧
    ∃ before position, observedStreamRep rep position before ∧
      position.output = expectedOutput input ∧
      ((outcome = .exited 0 ∧ (observedHost host).exit before 0 final) ∨
        ∃ message, outcome = .trapped message ∧
          (observedHost host).exitTrap before 0 message final)

/-- Every terminal execution of `begin` and the process followed by the exit of its status writes
the bytes of `expectedOutput` and exits with status 0, or ends in a rejected exit of it. -/
theorem command_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (short : position.input.length < 2 ^ 32)
    (execution : ProcessCommandExec (observedHost host) begin process world trace outcome final) :
    CommandResult host rep position.input outcome final := by
  have observed : observedStreamRep rep position world :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  cases execution with
  | next started continued finished =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at started
      cases started
      change Process.Exec (observedHost host) process initial _ _ _ _ at continued
      obtain ⟨nextPosition, nextRep, returned, output, _⟩ :=
        process_exec_correct streams.observed short continued observed
          (future_initial position empty)
      cases returned
      change LeanExe.Wasi.Exec (observedHost host) (Action.exit (α := Unit) 0) _ _ _ _ at finished
      have code : exitStatus 0 = 0 := by decide
      cases finished with
      | exit accepted =>
          have finalOutput := StreamFold.observedStreamRep_exit_output nextRep accepted
          rw [code] at accepted ⊢
          exact ⟨finalOutput.symm.trans output, _, nextPosition, nextRep, output,
            Or.inl ⟨rfl, accepted⟩⟩
      | exitTrap rejected =>
          have finalOutput := StreamFold.observedStreamRep_exitTrap_output nextRep rejected
          rw [code] at rejected
          exact ⟨finalOutput.symm.trans output, _, nextPosition, nextRep, output,
            Or.inr ⟨_, rfl, rejected⟩⟩
  | beginExit execution =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at execution
      cases execution
  | beginTrap execution =>
      change LeanExe.Wasi.Exec (observedHost host) (.pure (⟨true, 0, initial⟩ : ProcessStep State))
        _ _ _ _ at execution
      cases execution

theorem result_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : Observed World}
    (represented : rep position world.world) (events : world.events = [])
    (empty : position.output = []) (short : position.input.length < 2 ^ 32)
    (accepted : ExitAccepted host rep) {final : Store (Observed World)} {message : String}
    (total : TargetTerminated host (.Trap final message))
    (native : ProcessEntryRunResult (observedHost host) begin process world (.Trap final message)) :
    stdoutWords final.host.events = expectedOutput position.input ∧
      host.exited final.host.world = some 0 := by
  change ProcessEntryResult (observedHost host) begin process world (.Trap final message) at native
  cases native with
  | terminal final trace outcome message execution terminal =>
      obtain ⟨output, before, nextPosition, nextRep, _, finished⟩ :=
        command_output streams represented events empty short execution
      rcases finished with ⟨returned, operation⟩ | ⟨error, trapped, operation⟩
      · exact ⟨output, host.exit_recorded operation.1⟩
      · have code : exitStatus 0 = 0 := by decide
        rw [← code] at operation
        exact False.elim (accepted nextPosition before nextRep _ rfl error _ operation)
  | resource final trace residual progress =>
      have impossible : ("unreachable" : String) = exitTrap := total.1
      exact False.elim ((by decide : ("unreachable" : String) ≠ exitTrap) impossible)

theorem memoryCap_pure {α : Type} (store : Store α) :
    store.memoryCap module 0 = store.memoryCap io.pure.module 0 :=
  PureTransport.memoryCap_zero_eq rfl store

/-- From a store with an allocator at `heap`, the literal pool, and room above `heap.top` for two
copies of a state and the charge of a step for an input of at most `L` bytes, the module's
`_start` exits with status 0 after writing exactly the bytes of the report of the input. -/
theorem terminates_of_room {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    {L : Nat} (size : position.input.length ≤ L)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    (room : heap.top.toNat + 2 * copyLimit L + stepCharge L ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 := by
  have small : L < 2 ^ 32 := by
    have := Nat.mul_le_mul_left 65536 cap
    unfold copyLimit stepCharge at room
    rw [memoryCap_pure] at this
    omega
  have short : position.input.length < 2 ^ 32 := by omega
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  have initialFuture := future_initial position empty
  have initialCopy := (initialFuture.sized size).copyCost
  have beginEq := beginCharge_eq
  obtain ⟨bound, executions⟩ := target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress (Future position.input) (charge_advances streams short)
    observed initialFuture valid at_ free static cap (fun _ _ => stepCharge L) beginCharge
    (by unfold stepCharge at room; omega)
    (begin_prefix_bound (observedHost host) initial.host)
    (fun native ghost world _ _ _ future => by
      have copy := (future.sized size).copyCost
      exact ⟨by omega, step_prefix_bound (observedHost host) small (future.sized size) world⟩)
    (fun native ghost world _ represented _ future _ next final _ execution _ => by
      have copy := (future.sized size).copyCost
      have nextCopy :=
        (step_sized streams.observed short size represented future execution).copyCost
      omega)
    accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed : run fuel module startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      exact ⟨final, by simp [messageEq],
        result_output streams represented events empty short accepted total native⟩
  | _ => exact total.elim

set_option maxHeartbeats 2000000 in
theorem initial_memoryCap {World : Type} (world : Observed World) :
    (PureTransport.erase (initialStore world)).memoryCap io.pure.module 0 = 65535 := by
  rw [initialStore, PureTransport.erase_restore]
  decide +kernel

theorem initial_top : (initialStaticHeap io.literalPool).top.toNat = 4096 := by
  decide +kernel

/-- The bytes above the literal pool that a run on an input of at most `L` bytes needs: two copies
of a state and the charge of a step. -/
def processMemory (L : Nat) : Nat := 2 * copyLimit L + stepCharge L

theorem processMemory_eq (L : Nat) : processMemory L = 84 * L + 37614624 := by
  simp only [processMemory, stepCharge, copyLimit]
  omega

/-- For every input of at most `L` bytes, when `processMemory L` bytes fit in the module's memory
of 65,535 pages above the literal pool, which ends at 4,096 bytes, under StreamFold's host
assumptions, a Talos host that satisfies the import specifications, and a host that accepts the
exit status 0, the compiled command from its initial store exits with status 0 after writing
exactly the bytes of the report of the input. -/
theorem initial_terminates {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    {L : Nat} (size : position.input.length ≤ L) (room : 4096 + processMemory L ≤ 65536 * 65535)
    (valid : targetHost.Satisfies module (hostSpec host)) (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 :=
  terminates_of_room host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty size valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1
    (by rw [initial_top, initial_memoryCap]; unfold processMemory at room; omega) accepted

/-- `initial_terminates` for every input of at most 50,000,000 bytes. -/
theorem initial_terminates_50000000 {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (size : position.input.length ≤ 50000000)
    (valid : targetHost.Satisfies module (hostSpec host)) (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some 0 :=
  initial_terminates host targetHost world rep streams represented events empty size
    (by rw [processMemory_eq]; omega) valid accepted

/-- One byte sequence encodes the module, decodes to it, and is a valid binary, and the module
satisfies `initial_terminates`. -/
theorem terminates_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates⟩

end Demos.Rcv.Process
