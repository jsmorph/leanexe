import Demos.StreamFold.Rank
import Verified.Wasi.ProcessTotalSource

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

structure StreamProgress {World Ghost : Type} (host : Host World) (rep : Ghost → World → Prop)
    (unread zeroWrites : Ghost → Nat) : Prop where
  read_available : ∀ ghost world, rep ghost world →
    ∃ bytes final, host.read world 4096 (.returned 0 bytes) final
  write_available : ∀ ghost world bytes, rep ghost world → 0 < bytes.data.size →
    ∃ count final, host.write world .stdout bytes (.returned 0 count) final
  read_reply : ∀ {ghost world reply final}, rep ghost world →
    host.read world 4096 reply final →
    ∃ bytes nextGhost, reply = .returned 0 bytes ∧ rep nextGhost final ∧
      unread nextGhost ≤ unread ghost ∧
      (bytes.data.size ≠ 0 → unread nextGhost < unread ghost)
  write_reply : ∀ {ghost world bytes reply final}, rep ghost world → 0 < bytes.data.size →
    host.write world .stdout bytes reply final →
    ∃ count nextGhost, reply = .returned 0 count ∧ rep nextGhost final ∧
      unread nextGhost = unread ghost ∧
      (count = 0 → zeroWrites nextGhost < zeroWrites ghost)

variable {Acc : Type} {kernel : Kernel Acc} {seed : Acc}

def Advances (rep : Ghost → World → Prop) (unread zeroWrites : Ghost → Nat)
    (state : (BufferState Acc)) (ghost : Ghost) (next : ProcessStep (BufferState Acc)) (final : World) : Prop :=
  ∃ nextGhost, rep nextGhost final ∧ Safe next.state ∧
    (next.running = false → next.status = 0 ∨ next.status = 28) ∧
    (next.running = true →
      RankLt (rank unread zeroWrites next.state nextGhost) (rank unread zeroWrites state ghost))

theorem remainingOutput_nonempty {state : (BufferState Acc)} (safe : Safe state)
    (pending : state.written < state.output.size) : 0 < (remainingOutput state).data.size := by
  rw [remainingOutput_size safe]
  have less := UInt64.lt_iff_toNat_lt.mp pending
  rw [safe.output_toNat] at less
  omega

theorem writeStep_advances {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : (BufferState Acc)} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (ready : rep ghost world) (safe : Safe state)
    (pending : state.written < state.output.size)
    (execution : LeanExe.Wasi.Exec host (writeStep state) world trace (.returned next) final) :
    Advances rep unread zeroWrites state ghost next final := by
  change LeanExe.Wasi.Exec host
    (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
    world trace (.returned next) final at execution
  cases execution with
  | write_return operation continuation =>
      cases continuation
      obtain ⟨count, nextGhost, replyEq, nextRep, sameInput, zeroDrop⟩ :=
        progress.write_reply ready (remainingOutput_nonempty safe pending) operation
      cases replyEq
      simp only [writeResult, ↓reduceIte]
      have countBound := (host.write_bound operation).1
      refine ⟨nextGhost, nextRep, afterWrite_safe safe _ countBound, ?_, ?_⟩
      · intro stopped
        simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at stopped
        split at stopped <;> exact Bool.noConfusion stopped
      · intro _
        exact rank_afterWrite unread zeroWrites safe pending _ countBound sameInput zeroDrop

theorem readStep_advances {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : (BufferState Acc)} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (ready : rep ghost world) (safe : Safe state)
    (eof : state.eof = false)
    (execution : LeanExe.Wasi.Exec host (readStep state) world trace (.returned next) final) :
    Advances rep unread zeroWrites state ghost next final := by
  change LeanExe.Wasi.Exec host
    (.read 4096 fun reply => .pure (afterRead state reply))
    world trace (.returned next) final at execution
  cases execution with
  | read_reject capacity continuation =>
      exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
  | read_return capacity operation continuation =>
      cases continuation
      obtain ⟨bytes, nextGhost, replyEq, nextRep, inputLe, nonemptyDrop⟩ :=
        progress.read_reply ready operation
      cases replyEq
      simp only [readResult, ↓reduceIte]
      have bytesBound := (host.read_bound operation).1
      refine ⟨nextGhost, nextRep, afterRead_safe safe _ bytesBound, ?_, ?_⟩
      · intro stopped
        simp [afterRead] at stopped
      · intro _
        exact rank_afterRead unread zeroWrites eof inputLe nonemptyDrop

theorem step_advances (spec : KernelSpec kernel) {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : (BufferState Acc)} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)} (ready : rep ghost world) (safe : Safe state)
    (execution : LeanExe.Wasi.Exec host (step kernel state) world trace (.returned next) final) :
    Advances rep unread zeroWrites state ghost next final := by
  by_cases pending : state.written < state.output.size
  · have code : step kernel state = writeStep state := by simp [step, pending]
    rw [code] at execution
    exact writeStep_advances progress ready safe pending execution
  · by_cases remaining : state.cursor < state.input.size
    · have code : step kernel state = .pure (consumeInput kernel state) := by simp [step, pending, remaining] <;> rfl
      rw [code] at execution
      cases execution
      have empty : state.output.size = 0 := by
        simp [Bytes.size, (safe.no_output pending).1]
      exact ⟨ghost, ready, (consumeInput_safe spec safe).1,
        fun stopped => Or.inr (consumeInput_stopped state stopped),
        fun _ => rank_consumeInput spec unread zeroWrites ghost safe empty remaining⟩
    · cases eof : state.eof with
      | false =>
          have code : step kernel state = readStep state := by simp [step, pending, remaining, eof]
          rw [code] at execution
          exact readStep_advances progress ready safe eof execution
      | true =>
          by_cases line : state.line.size.toUInt64 = 0
          · have code : step kernel state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, line] <;> rfl
            rw [code] at execution
            cases execution
            exact ⟨ghost, ready, safe, fun _ => Or.inl rfl,
              fun impossible => False.elim (Bool.noConfusion impossible)⟩
          · have code : step kernel state = .pure (completeLine kernel state) := by
              simp [step, pending, remaining, eof, line] <;> rfl
            rw [code] at execution
            cases execution
            exact ⟨ghost, ready, completeLine_safe spec safe,
              fun stopped => Or.inr (completeLine_stopped state stopped),
              fun running => rank_completeLine (kernel := kernel) unread zeroWrites ghost line running⟩

theorem step_exists {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : (BufferState Acc)} {ghost : Ghost} {world : World}
    (ready : rep ghost world) (safe : Safe state) :
    ∃ next trace final, LeanExe.Wasi.Exec host (step kernel state) world trace (.returned next) final := by
  by_cases pending : state.written < state.output.size
  · obtain ⟨count, final, operation⟩ :=
      progress.write_available ghost world (remainingOutput state) ready
        (remainingOutput_nonempty safe pending)
    refine ⟨afterWrite state ⟨0, count⟩,
      [.write .stdout (remainingOutput state) (.returned 0 count)], final, ?_⟩
    have code : step kernel state = writeStep state := by simp [step, pending]
    rw [code]
    exact .write_return operation (.pure final _)
  · by_cases remaining : state.cursor < state.input.size
    · refine ⟨consumeInput kernel state, [], world, ?_⟩
      have code : step kernel state = .pure (consumeInput kernel state) := by simp [step, pending, remaining] <;> rfl
      rw [code]
      exact .pure world _
    · cases eof : state.eof with
      | false =>
          obtain ⟨bytes, final, operation⟩ := progress.read_available ghost world ready
          refine ⟨afterRead state ⟨0, bytes⟩, [.read 4096 (.returned 0 bytes)], final, ?_⟩
          have code : step kernel state = readStep state := by simp [step, pending, remaining, eof]
          rw [code]
          exact .read_return (by decide) operation (.pure final _)
      | true =>
          by_cases line : state.line.size.toUInt64 = 0
          · refine ⟨⟨false, 0, state⟩, [], world, ?_⟩
            have code : step kernel state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, line] <;> rfl
            rw [code]
            exact .pure world _
          · refine ⟨completeLine kernel state, [], world, ?_⟩
            have code : step kernel state = .pure (completeLine kernel state) := by
              simp [step, pending, remaining, eof, line] <;> rfl
            rw [code]
            exact .pure world _

theorem step_returned {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {state : (BufferState Acc)} {ghost : Ghost} {world final : World} {trace : List Event}
    {outcome : Outcome (ProcessStep (BufferState Acc))} (ready : rep ghost world) (safe : Safe state)
    (execution : LeanExe.Wasi.Exec host (step kernel state) world trace outcome final) :
    ∃ next, outcome = .returned next := by
  by_cases pending : state.written < state.output.size
  · have code : step kernel state = writeStep state := by simp [step, pending]
    rw [code] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
      world trace outcome final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        exact ⟨_, rfl⟩
    | write_trap operation =>
        obtain ⟨_, _, impossible, _⟩ :=
          progress.write_reply ready (remainingOutput_nonempty safe pending) operation
        cases impossible
  · by_cases remaining : state.cursor < state.input.size
    · have code : step kernel state = .pure (consumeInput kernel state) := by
        simp [step, pending, remaining] <;> rfl
      rw [code] at execution
      cases execution
      exact ⟨_, rfl⟩
    · cases eof : state.eof with
      | false =>
          have code : step kernel state = readStep state := by simp [step, pending, remaining, eof]
          rw [code] at execution
          change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead state reply))
            world trace outcome final at execution
          cases execution with
          | read_reject capacity continuation =>
              exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
          | read_return capacity operation continuation =>
              cases continuation
              exact ⟨_, rfl⟩
          | read_trap capacity operation =>
              obtain ⟨_, _, impossible, _⟩ := progress.read_reply ready operation
              cases impossible
      | true =>
          by_cases line : state.line.size.toUInt64 = 0
          · have code : step kernel state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, line] <;> rfl
            rw [code] at execution
            cases execution
            exact ⟨_, rfl⟩
          · have code : step kernel state = .pure (completeLine kernel state) := by
              simp [step, pending, remaining, eof, line] <;> rfl
            rw [code] at execution
            cases execution
            exact ⟨_, rfl⟩

theorem process_terminates (spec : KernelSpec kernel) {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {unread zeroWrites : Ghost → Nat}
    (progress : StreamProgress host rep unread zeroWrites)
    {state : (BufferState Acc)} {ghost : Ghost} {world : World} (ready : rep ghost world) (safe : Safe state) :
    ∃ trace status final finalGhost,
      Process.Exec host (process kernel seed) state world trace (.returned status) final ∧
      (status = 0 ∨ status = 28) ∧ rep finalGhost final := by
  let represented (config : (BufferState Acc) × Ghost) (state : (BufferState Acc)) (world : World) : Prop :=
    config.1 = state ∧ rep config.2 world ∧ Safe state
  let measure (config : (BufferState Acc) × Ghost) := rank unread zeroWrites config.1 config.2
  obtain ⟨trace, status, final, config, finalState, execution, statusOk, finalRep⟩ :=
    Process.exec_of_wellFounded (host := host) (process := process kernel seed) represented
      (InvImage RankLt measure) (InvImage.wf measure rank_wellFounded)
      (fun status => status = 0 ∨ status = 28)
      (fun config current world held => by
        obtain ⟨state, ghost⟩ := config
        obtain ⟨rfl, ready, safe⟩ := held
        obtain ⟨next, trace, final, execution⟩ := step_exists progress ready safe
        obtain ⟨nextGhost, nextRep, nextSafe, statusOk, smaller⟩ :=
          step_advances spec progress ready safe execution
        exact ⟨next, trace, final, (next.state, nextGhost), execution,
          ⟨rfl, nextRep, nextSafe⟩, statusOk, smaller⟩)
      (ghost := (state, ghost)) (state := state) (world := world) ⟨rfl, ready, safe⟩
  exact ⟨trace, status, final, config.2, execution, statusOk, finalRep.2.1⟩

theorem initial_terminates (spec : KernelSpec kernel) {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {unread zeroWrites : Ghost → Nat}
    (progress : StreamProgress host rep unread zeroWrites)
    {ghost : Ghost} {world : World} (ready : rep ghost world) :
    ∃ trace status final finalGhost,
      Process.Exec host (process kernel seed) (initial seed) world trace (.returned status) final ∧
      (status = 0 ∨ status = 28) ∧ rep finalGhost final :=
  process_terminates spec progress ready (Safe.initial seed)

end Demos.StreamFold
