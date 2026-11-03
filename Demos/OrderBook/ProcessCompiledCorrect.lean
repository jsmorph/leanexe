import Demos.OrderBook.ProcessCharges
import Demos.OrderBook.ProcessCorrect
import Demos.OrderBook.ProcessTermination
import Demos.StreamFold.Observed
import Verified.Wasi.ProcessEntryProofs

/-! The correctness of the compiled process.  Under StreamFold's host assumptions, a Talos host
that satisfies the three import specifications, a host that accepts the exit statuses 0 and 28, and
the requirements' bound of fewer than 2^64 - 1 records, `initial_terminates` states that the
module's `_start` exits after writing exactly the bytes of `expectedOutput` of the input, with the
status `expectedStatus` of it.  The memory condition is a closed inequality, `initial_room`, with
`run`'s bound on 74 records from any book of the program's sizes, `Bound.runBoundSized 74`, since
the charge of a read step holds for every reply and so cannot depend on the input's records. -/

namespace Demos.OrderBook.Process

open Wasm _root_.Verified _root_.Verified.Wasi LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime
open Demos.StreamFold (StreamPosition StreamHost observedStreamRep stdoutWords)

/-- The host accepts the exit statuses 0 and 28 at every represented world. -/
def ExitAccepted {World : Type} (host : Host World)
    (rep : StreamPosition → World → Prop) : Prop :=
  ∀ position world, observedStreamRep rep position world → ∀ status,
    status = 0 ∨ status = 28 → ∀ message final,
    (observedHost host).exitTrap world (exitStatus status) message final → False

theorem expectedStatus_cases (input : List UInt64) :
    expectedStatus input = 0 ∨ expectedStatus input = 28 := by
  unfold expectedStatus
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem expectedStatus_exit (input : List UInt64) :
    exitStatus (expectedStatus input) = expectedStatus input := by
  rcases expectedStatus_cases input with same | same <;> rw [same] <;> decide

/-- A step from a state with the invariant keeps it, at a lower rank while the process runs, with
one next stream position for both. -/
theorem future_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position : StreamPosition} {processed : List UInt64}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position processed)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → (∃ processed', Future input next.state nextPosition processed') ∧
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
          ⟨⟨processed, future_afterWrite future _ bound sameInput output⟩,
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
              ⟨future_readStep ids future pending eof (host.read_bound operation).1 consumed atEof
                sameOutput,
                rank_afterRead _ _ eof (by omega) (fun _ => by omega)⟩⟩

/-- The invariant of the charges: the state has a future for the input. -/
def ChargeInv (input : List UInt64) (s : State) (position : StreamPosition) : Prop :=
  ∃ processed, Future input s position processed

theorem charge_advances {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1) :
    StepAdvances (observedHost host) (observedStreamRep rep) (fun position => position.input.length)
      StreamPosition.zeroWrites (ChargeInv input) := by
  intro s position world final trace next _ invariant represented execution
  obtain ⟨processed, future⟩ := invariant
  obtain ⟨nextPosition, nextRep, after⟩ :=
    future_advances streams.observed ids represented future execution
  exact ⟨nextPosition, nextRep, fun running => after running⟩

def CommandResult {World : Type} (host : Host World) (rep : StreamPosition → World → Prop)
    (input : List UInt64) (outcome : Outcome Unit) (final : Observed World) : Prop :=
  stdoutWords final.events = expectedOutput input ∧
    ∃ before position, observedStreamRep rep position before ∧
      position.output = expectedOutput input ∧
      ((outcome = .exited (expectedStatus input) ∧
          (observedHost host).exit before (expectedStatus input) final) ∨
        ∃ message, outcome = .trapped message ∧
          (observedHost host).exitTrap before (expectedStatus input) message final)

/-- Every terminal execution of `begin` and the process followed by the exit of its status writes
the bytes of `expectedOutput` and exits with `expectedStatus`, or ends in a rejected exit of it. -/
theorem command_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : Observed World} {trace : List Event}
    {outcome : Outcome Unit} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (ids : (Spec.records (leWords position.input)).length < 2 ^ 64 - 1)
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
        process_exec_correct streams.observed ids continued observed (future_initial position empty)
      cases returned
      change LeanExe.Wasi.Exec (observedHost host)
        (Action.exit (α := Unit) (expectedStatus position.input)) _ _ _ _ at finished
      have code := expectedStatus_exit position.input
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
    (empty : position.output = [])
    (ids : (Spec.records (leWords position.input)).length < 2 ^ 64 - 1)
    (accepted : ExitAccepted host rep) {final : Store (Observed World)} {message : String}
    (total : TargetTerminated host (.Trap final message))
    (native : ProcessEntryRunResult (observedHost host) begin process world (.Trap final message)) :
    stdoutWords final.host.events = expectedOutput position.input ∧
      host.exited final.host.world = some (expectedStatus position.input) := by
  change ProcessEntryResult (observedHost host) begin process world (.Trap final message) at native
  cases native with
  | terminal final trace outcome message execution terminal =>
      obtain ⟨output, before, nextPosition, nextRep, _, finished⟩ :=
        command_output streams represented events empty ids execution
      rcases finished with ⟨returned, operation⟩ | ⟨error, trapped, operation⟩
      · exact ⟨output, host.exit_recorded operation.1⟩
      · rw [← expectedStatus_exit] at operation
        exact False.elim (accepted nextPosition before nextRep _
          (expectedStatus_cases position.input) error _ operation)
  | resource final trace residual progress =>
      have impossible : ("unreachable" : String) = exitTrap := total.1
      exact False.elim ((by decide : ("unreachable" : String) ≠ exitTrap) impossible)

theorem memoryCap_pure {α : Type} (store : Store α) :
    store.memoryCap module 0 = store.memoryCap io.pure.module 0 :=
  PureTransport.memoryCap_zero_eq rfl store

/-- From a store with an allocator at `heap`, the literal pool, and room above `heap.top` for two
copies of a state and the charge of a step, when the input holds fewer than 2^64 - 1 records and
`RunBound R` holds, the module's `_start` exits after writing exactly the
bytes of `expectedOutput` of the input, with the status `expectedStatus` of it. -/
theorem terminates_of_room {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (initial : Store (Observed World)) (heap : Heap)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position initial.host.world)
    (events : initial.host.events = []) (empty : position.output = [])
    (ids : (Spec.records (leWords position.input)).length < 2 ^ 64 - 1)
    (valid : targetHost.Satisfies module (hostSpec host))
    (at_ : heap.At (PureTransport.erase initial)) (free : heap.free = [])
    (static : io.literalPool.Static heap (PureTransport.erase initial))
    (cap : (PureTransport.erase initial).memoryCap module 0 ≤ 65535)
    {R : Nat} (runBound : RunBound R)
    (room : heap.top.toNat + 2 * copyLimit + stepCharge R ≤
      65536 * (PureTransport.erase initial).memoryCap io.pure.module 0)
    (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex initial [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some (expectedStatus position.input) := by
  have observed : observedStreamRep rep position initial.host :=
    ⟨represented, by simp [empty, events, stdoutWords]⟩
  have initialFuture := future_initial position empty
  have initialCopy := initialFuture.sized.copyCost
  have beginEq := beginCharge_eq
  have limitEq : copyLimit = 197205 + outputLimit := rfl
  have chargeEq : stepCharge R = copyLimit + R + 21435213 := rfl
  obtain ⟨bound, executions⟩ := target_terminates host targetHost initial heap
    (observedStreamRep rep) (fun position => position.input.length) StreamPosition.zeroWrites
    streams.observed.progress (ChargeInv position.input) (charge_advances streams ids)
    observed ⟨[], initialFuture⟩ valid at_ free static cap (fun _ _ => stepCharge R) beginCharge
    (by omega)
    (begin_prefix_bound (observedHost host) initial.host)
    (fun native ghost world _ _ _ invariant => by
      obtain ⟨processed, future⟩ := invariant
      have copy := future.sized.copyCost
      exact ⟨by omega, step_prefix_bound (observedHost host) runBound future.sized world⟩)
    (fun native ghost world _ represented _ invariant _ next final _ execution _ => by
      obtain ⟨processed, future⟩ := invariant
      have copy := future.sized.copyCost
      have nextCopy :=
        (step_sized streams.observed ids represented future execution).copyCost
      omega)
    accepted
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨total, native⟩ := executions fuel enough
  generalize executed : run fuel module startIndex initial [] targetHost = result at total native ⊢
  cases result with
  | Trap final message =>
      have messageEq := total.1
      exact ⟨final, by simp [messageEq],
        result_output streams represented events empty ids accepted total native⟩
  | _ => exact total.elim

set_option maxHeartbeats 2000000 in
theorem initial_memoryCap {World : Type} (world : Observed World) :
    (PureTransport.erase (initialStore world)).memoryCap io.pure.module 0 = 65535 := by
  show (module.initialStore : Store Unit).memoryCap io.pure.module 0 = 65535
  decide +kernel

theorem initial_top : (initialStaticHeap io.literalPool).top.toNat = 4096 := by
  decide +kernel

/-- The memory that a run needs fits in 65,535 pages: two copies of a state and a step's charge
with `run`'s bound on 74 records from any book of the program's sizes total 3,456,119,748 bytes
above the literal pool, which ends at 4,096 bytes, and the sum lies below the 4,294,901,760 bytes
of 65,535 pages. -/
theorem initial_room :
    4096 + 2 * copyLimit + stepCharge (Bound.runBoundSized 74) ≤ 65536 * 65535 := by
  decide

/-- For every input of fewer than 2^64 - 1 records, under StreamFold's host assumptions, a Talos
host that satisfies the import specifications, and a host that accepts the exit statuses 0 and 28,
the compiled command from its initial store exits after writing exactly the little-endian bytes of
the event words of `Spec.run` from the empty book on the whole words of the input, with status 0
when the input fills whole words and 28 otherwise. -/
theorem initial_terminates {World : Type} (host : Host World)
    (targetHost : HostEnv (Observed World)) (world : Observed World)
    (rep : StreamPosition → World → Prop) (streams : StreamHost host rep)
    {position : StreamPosition} (represented : rep position world.world)
    (events : world.events = []) (empty : position.output = [])
    (ids : (Spec.records (leWords position.input)).length < 2 ^ 64 - 1)
    (valid : targetHost.Satisfies module (hostSpec host)) (accepted : ExitAccepted host rep) :
    ∃ bound, ∀ fuel ≥ bound, ∃ final,
      run fuel module startIndex (initialStore world) [] targetHost = .Trap final exitTrap ∧
        stdoutWords final.host.events = expectedOutput position.input ∧
        host.exited final.host.world = some (expectedStatus position.input) :=
  terminates_of_room host targetHost (initialStore world) (initialStaticHeap io.literalPool)
    rep streams represented events empty ids valid
    (initialState world).1 rfl (initialState world).2.2 (initialState world).2.1 runBound_74
    (by rw [initial_top, initial_memoryCap]; exact initial_room) accepted

/-- One byte sequence encodes the module, decodes to it, and is a valid binary, and the module
satisfies `initial_terminates`. -/
theorem terminates_bytes : ∃ bytes,
    Encoding.encode module = .ok bytes ∧ Encoding.decode bytes = .ok module ∧
      Encoding.ValidBinary bytes ∧ (type_of% @initial_terminates) := by
  obtain ⟨bytes, encoded, decoded, valid, _⟩ := command.bytes
  exact ⟨bytes, encoded, decoded, valid, @initial_terminates⟩

end Demos.OrderBook.Process
