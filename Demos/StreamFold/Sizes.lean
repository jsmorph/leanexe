import Demos.StreamFold.Future

/-! Bounds on the sizes of a stream process's state: its pending line, from the rooms that its
future needs, and its input and output buffers, which every step keeps within the read capacity
and a bound on the kernel's output for the current total. -/

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc}

/-- When each room bounds a line by `bound`, the model's pending line is at most `bound` long,
since it is a prefix of the line that ends at the next LF or at the end of the input. -/
theorem Model.pending_le (spec : KernelSpec kernel) (bound : Nat)
    (fits : ∀ {total line}, spec.Room total line → line.size ≤ bound) :
    ∀ (bytes : List UInt64) (state : Model.State Acc), Model.Safe spec state bytes →
      (∀ final, Model.consume kernel state bytes = .ok final → final.pending.size ≠ 0 →
        spec.Room final.total final.pending) → state.pending.size ≤ bound
  | [], state, _, finalRoom => by
      by_cases empty : state.pending.size = 0
      · omega
      · exact fits (finalRoom state rfl empty)
  | byte :: bytes, state, safe, finalRoom => by
      by_cases newline : byte = 10
      · exact fits (safe.1 newline)
      · have next : Model.consumeByte kernel state byte =
            .ok { state with pending := state.pending.push byte } := by
          simp [Model.consumeByte, newline]
        have longer := pending_le spec bound fits bytes _ (safe.2 _ next)
          (fun final executed nonempty => finalRoom final
            (by rw [Model.consume_cons, next]; exact executed) nonempty)
        simp only [Array.size_push] at longer
        omega

theorem StreamFuture.line_le (spec : KernelSpec kernel) (bound : Nat)
    (fits : ∀ {total line}, spec.Room total line → line.size ≤ bound)
    {state : BufferState Acc} {position : StreamPosition} {history expected : List Bytes}
    {status : UInt64} (future : StreamFuture spec state position history expected status) :
    state.line.size ≤ bound :=
  Model.pending_le spec bound fits _ (bufferModel state history) future.modelSafe future.finalRoom

/-- The input buffer holds at most one read's 4,096 bytes, and the output buffer at most `size`
of the current total. -/
structure Within (size : Acc → Nat) (state : BufferState Acc) : Prop where
  input : state.input.data.size ≤ 4096
  output : state.output.data.size ≤ size state.total

theorem Within.initial (size : Acc → Nat) (seed : Acc) : Within size (initial seed) :=
  ⟨Nat.zero_le _, Nat.zero_le _⟩

variable {size : Acc → Nat}
  (kernelOutput : ∀ total line, (kernel total line).valid = true →
    (kernel total line).output.data.size ≤ size (kernel total line).total)

include kernelOutput in
theorem completeLine_within {state : BufferState Acc} (within : Within size state) :
    Within size (completeLine kernel state).state := by
  cases accepted : (kernel state.total state.line).valid with
  | false => simpa only [completeLine, accepted, Bool.not_false, ↓reduceIte] using within
  | true =>
      simp only [completeLine, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨within.input, kernelOutput _ _ accepted⟩

include kernelOutput in
theorem consumeStep_within {current : ProcessStep (BufferState Acc)}
    (within : Within size current.state) : Within size (consumeStep kernel current).state := by
  dsimp only [consumeStep]
  split
  · exact completeLine_within kernelOutput ⟨within.input, within.output⟩
  · exact ⟨within.input, within.output⟩

include kernelOutput in
theorem consumeInput_within {state : BufferState Acc} (within : Within size state) :
    Within size (consumeInput kernel state).state := by
  suffices preserved : ∀ fuel (current : ProcessStep (BufferState Acc)),
      Within size current.state →
      Within size (LeanExe.repeatWhile.go consumeTest (consumeStep kernel) fuel current).state from
    preserved _ ⟨true, 0, state⟩ within
  intro fuel
  induction fuel with
  | zero => exact fun _ within => within
  | succ fuel ih =>
      intro current within
      simp only [LeanExe.repeatWhile.go]
      split
      · exact ih _ (consumeStep_within kernelOutput within)
      · exact within

theorem afterWrite_within {state : BufferState Acc} (within : Within size state)
    (reply : WriteResult) : Within size (afterWrite state reply).state := by
  unfold afterWrite
  dsimp only
  split
  · exact within
  · split
    · exact ⟨within.input, Nat.zero_le _⟩
    · exact ⟨within.input, within.output⟩

theorem afterRead_within {state : BufferState Acc} (within : Within size state)
    {errno : UInt64} {bytes : Bytes} (bound : bytes.data.size ≤ (4096 : UInt64).toNat) :
    Within size (afterRead state (readResult errno bytes)).state := by
  by_cases zero : errno = 0
  · subst zero
    simp only [afterRead, readResult, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
    exact ⟨by simpa using bound, within.output⟩
  · have failed : (errno != 0) = true := by simpa using zero
    simp only [afterRead, readResult, failed, ↓reduceIte]
    exact within

include kernelOutput in
/-- Every step that returns keeps the buffers within their bounds, whatever the host replies. -/
theorem step_within {World : Type} {host : Host World} {state : BufferState Acc}
    {world final : World} {trace : List Event} {next : ProcessStep (BufferState Acc)}
    (within : Within size state)
    (execution : LeanExe.Wasi.Exec host (step kernel state) world trace (.returned next) final) :
    Within size next.state := by
  by_cases pending : state.written < state.output.size
  · have code : step kernel state = writeStep state := by simp [step, pending]
    rw [code] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
      world trace (.returned next) final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        exact afterWrite_within within _
  · by_cases remaining : state.cursor < state.input.size
    · have code : step kernel state = .pure (consumeInput kernel state) := by
        simp [step, pending, remaining]
        rfl
      rw [code] at execution
      cases execution
      exact consumeInput_within kernelOutput within
    · cases eof : state.eof with
      | false =>
          have code : step kernel state = readStep state := by simp [step, pending, remaining, eof]
          rw [code] at execution
          change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead state reply))
            world trace (.returned next) final at execution
          cases execution with
          | read_reject capacity continuation =>
              exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
          | read_return capacity operation continuation =>
              cases continuation
              exact afterRead_within within (host.read_bound operation).1
      | true =>
          by_cases empty : state.line.size.toUInt64 = 0
          · have code : step kernel state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            exact within
          · have code : step kernel state = .pure (completeLine kernel state) := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            exact completeLine_within kernelOutput within

/-- Where the model stops at a rejected line, its total is good and the line has its room. -/
theorem Model.error_room (spec : KernelSpec kernel) :
    ∀ (bytes : List UInt64) (state : Model.State Acc) {stopped : Model.State Acc},
      Model.Safe spec state bytes → spec.Good state.total →
      Model.consume kernel state bytes = .error stopped →
      spec.Good stopped.total ∧ spec.Room stopped.total stopped.pending
  | [], state, _, _, _, executed => by
      rw [Model.consume_nil] at executed
      cases executed
  | byte :: bytes, state, stopped, safe, good, executed => by
      by_cases newline : byte = 10
      · have room := safe.1 newline
        cases accepted : (kernel state.total state.pending).valid with
        | false =>
            have same : stopped = state := by
              simpa [Model.consume_cons, Model.consumeByte, Model.emitLine, newline, accepted, bind,
                Except.bind] using executed.symm
            subst same
            exact ⟨good, room⟩
        | true =>
            have next : Model.consumeByte kernel state byte =
                .ok ⟨(kernel state.total state.pending).total, #[],
                  state.output ++ [(kernel state.total state.pending).output]⟩ := by
              simp [Model.consumeByte, Model.emitLine, newline, accepted]
            rw [Model.consume_cons, next] at executed
            exact error_room spec bytes _ (safe.2 _ next) (spec.accepted good room accepted).1
              executed
      · have next : Model.consumeByte kernel state byte =
            .ok { state with pending := state.pending.push byte } := by
          simp [Model.consumeByte, newline]
        rw [Model.consume_cons, next] at executed
        exact error_room spec bytes _ (safe.2 _ next) good executed

theorem afterWrite_stopped {state : BufferState Acc} {reply : WriteResult}
    (stopped : (afterWrite state reply).running = false) :
    (afterWrite state reply).state = state := by
  revert stopped
  unfold afterWrite
  dsimp only
  split
  · exact fun _ => rfl
  · split <;> exact fun impossible => Bool.noConfusion impossible

theorem afterRead_stopped {state : BufferState Acc} {reply : ReadResult}
    (stopped : (afterRead state reply).running = false) :
    (afterRead state reply).state = state := by
  revert stopped
  unfold afterRead
  split
  · exact fun _ => rfl
  · exact fun impossible => Bool.noConfusion impossible

theorem completeLine_stopped_state {state : BufferState Acc}
    (stopped : (completeLine kernel state).running = false) :
    (completeLine kernel state).state = state := by
  revert stopped
  unfold completeLine
  dsimp only
  split
  · exact fun _ => rfl
  · exact fun impossible => Bool.noConfusion impossible

/-- A step that stops leaves a good total and a pending line that has its room, or the line of
the state before it. -/
theorem streamFuture_stopped (spec : KernelSpec kernel) (bound : Nat)
    (fits : ∀ {total line}, spec.Room total line → line.size ≤ bound)
    {World : Type} {host : Host World} {state : BufferState Acc} {position : StreamPosition}
    {history expected : List Bytes} {status : UInt64} {world final : World} {trace : List Event}
    {next : ProcessStep (BufferState Acc)}
    (future : StreamFuture spec state position history expected status)
    (execution : LeanExe.Wasi.Exec host (step kernel state) world trace (.returned next) final)
    (stopped : next.running = false) :
    spec.Good next.state.total ∧ next.state.line.size ≤ bound := by
  have before : spec.Good state.total ∧ state.line.size ≤ bound :=
    ⟨future.normal, future.line_le spec bound fits⟩
  by_cases pending : state.written < state.output.size
  · have code : step kernel state = writeStep state := by simp [step, pending]
    rw [code] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput state) fun reply => .pure (afterWrite state reply))
      world trace (.returned next) final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        rw [afterWrite_stopped stopped]
        exact before
  · by_cases remaining : state.cursor < state.input.size
    · have code : step kernel state = .pure (consumeInput kernel state) := by
        simp [step, pending, remaining]
        rfl
      rw [code] at execution
      cases execution
      have noOutput := future.safe.no_output pending
      have empty : state.output.size = 0 := by simp [Bytes.size, noOutput.1]
      have modelSafe := (Model.safe_append_iff spec _ (unreadWords state) position.input).mp
        future.modelSafe
      obtain ⟨consumed, progress⟩ := consumeInput_buffer spec state history future.safe empty
        future.normal modelSafe.1
      obtain ⟨_, executed⟩ := progress.stopped stopped
      have consumedSafe : Model.Safe spec (bufferModel state history) consumed := by
        have whole := modelSafe.1
        rw [progress.split] at whole
        exact ((Model.safe_append_iff spec _ consumed _).mp whole).1
      exact Model.error_room spec consumed _ consumedSafe future.normal executed |>.imp id fits
    · cases eof : state.eof with
      | false =>
          have code : step kernel state = readStep state := by simp [step, pending, remaining, eof]
          rw [code] at execution
          change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead state reply))
            world trace (.returned next) final at execution
          cases execution with
          | read_reject capacity continuation =>
              exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
          | read_return capacity operation continuation =>
              cases continuation
              rw [afterRead_stopped stopped]
              exact before
      | true =>
          by_cases empty : state.line.size.toUInt64 = 0
          · have code : step kernel state = .pure ⟨false, 0, state⟩ := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            exact before
          · have code : step kernel state = .pure (completeLine kernel state) := by
              simp [step, pending, remaining, eof, empty]
              rfl
            rw [code] at execution
            cases execution
            rw [completeLine_stopped_state stopped]
            exact before

end Demos.StreamFold
