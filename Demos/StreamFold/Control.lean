module

public import Demos.StreamFold.Interface

@[expose] public section

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc}

/-! ## The read of a step

A read step reads stdin into a fresh buffer of 4,096 bytes of 0.  `readStdin_fresh` states that
call as one read of capacity 4,096, and `filled_fresh` states that the copy of the bytes that the
read placed in the buffer is the bytes read, from the facts that `Exec.read_return` states about
the buffer's region after the call. -/

/-- The result that the read of a step passes on for the reply `reply` of the host. -/
def freshFill (reply : ReadReply) : FillResult :=
  FillResult.of (Bytes.build 4096 fun _ => 0) 0 4096 reply.errno reply.bytes.size reply.range

theorem readStdin_fresh :
    readStdin (Bytes.build 4096 fun _ => 0) 0 4096 =
      .read 4096 fun reply => .pure (freshFill reply) := by
  have length : (Bytes.build 4096 fun _ => 0).windowLength 0 4096 = 4096 := by
    simp only [Bytes.windowLength, Bytes.window_snd, Bytes.data_size_build]
    decide
  rw [readStdin, length]
  rfl

theorem bind_readStdin_fresh {α : Type} (next : FillResult → α) :
    Action.bind (readStdin (Bytes.build 4096 fun _ => 0) 0 4096) (fun reply => .pure (next reply)) =
      .read 4096 fun reply => .pure (next (freshFill reply)) := by
  rw [readStdin_fresh]
  rfl

/-- Byte `i` of an array whose first bytes are `bytes` is byte `i` of `bytes`. -/
theorem getElem_of_extract {array bytes : ByteArray} (first : array.extract 0 bytes.size = bytes)
    {i : Nat} (inside : i < bytes.size) (bound : i < array.size) : array[i] = bytes[i] := by
  have inExtract : i < (array.extract 0 bytes.size).size := by
    rw [ByteArray.size_extract]
    omega
  have element : (array.extract 0 bytes.size)[i]'inExtract = bytes[i] := by
    revert inExtract
    rw [first]
    intro _
    rfl
  simpa only [ByteArray.getElem_extract, Nat.zero_add] using element

/-- The bytes read fit in the region of 4,096 bytes that begins with them. -/
theorem fresh_le {committed range : Bytes} (size : range.data.size = (4096 : UInt64).toNat)
    (first : range.data.extract 0 committed.data.size = committed.data) :
    committed.data.size ≤ 4096 := by
  have extractSize := congrArg ByteArray.size first
  rw [ByteArray.size_extract, size] at extractSize
  simp only [UInt64.reduceToNat] at extractSize
  omega

/-- On errno 0, the read of a step passes errno 0, the number of bytes read, and the buffer with its
first bytes replaced by the region after the call. -/
theorem freshFill_zero (committed range : Bytes) :
    freshFill (readReply 0 committed range) =
      ⟨0, committed.size, (Bytes.build 4096 fun _ => 0).splice 0 range⟩ := by
  have firstPosition : ((Bytes.build 4096 fun _ => 0).window 0 4096).1 = 0 := by
    rw [Bytes.window_fst, Bytes.data_size_build]
    rfl
  simp only [freshFill, readReply, FillResult.of, ↓reduceIte, firstPosition]

/-- That buffer begins with the bytes read. -/
theorem fresh_splice_prefix {committed range : Bytes}
    (size : range.data.size = (4096 : UInt64).toNat)
    (first : range.data.extract 0 committed.data.size = committed.data) :
    ((Bytes.build 4096 fun _ => 0).splice 0 range).data.extract 0 committed.data.size =
      committed.data := by
  have bound := fresh_le size first
  have rangeLe : 0 + range.data.size ≤ (Bytes.build 4096 fun _ => 0).data.size := by
    rw [Bytes.data_size_build, size, Nat.zero_add]
    exact Nat.le_refl _
  have spliced := Bytes.splice_extract rangeLe (n := committed.data.size)
    (by rw [size]; simp only [UInt64.reduceToNat]; omega)
  rw [Nat.zero_add] at spliced
  rw [spliced, first]

/-- The copy of the first `bytes.size` bytes of a buffer that begins with `bytes` is `bytes`. -/
theorem build_prefix {buffer bytes : Bytes} (small : bytes.data.size < UInt64.size)
    (first : buffer.data.extract 0 bytes.data.size = bytes.data) :
    Bytes.build bytes.size (fun i => buffer.get i) = bytes := by
  have sizeNat := Bytes.size_toNat bytes small
  have extractSize := congrArg ByteArray.size first
  rw [ByteArray.size_extract] at extractSize
  have dataEq : (Bytes.build bytes.size fun i => buffer.get i).data = bytes.data := by
    apply ByteArray.ext
    apply Array.ext
    · simp only [ByteArray.size_data, Bytes.data_size_build, sizeNat]
    · intro i _ right
      have inside : i < bytes.data.size := by simpa using right
      have iNat : (UInt64.ofNat i).toNat = i :=
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans inside small)
      have inBuffer : i < buffer.data.size := by omega
      simp only [Bytes.build, Array.getElem_ofFn, Bytes.get, iNat, inBuffer, ↓reduceDIte,
        UInt8.toUInt8_toUInt64]
      simpa only [ByteArray.getElem_eq_getElem_data] using
        getElem_of_extract first inside inBuffer
  exact congrArg Bytes.mk dataEq

/-- The bytes that the read of a step placed are the bytes read, when the buffer's region after
the call has its 4,096 bytes and begins with the bytes read on errno 0. -/
theorem filled_fresh {errno : UInt64} {committed range : Bytes}
    (size : range.data.size = (4096 : UInt64).toNat)
    (first : errno = 0 → range.data.extract 0 committed.data.size = committed.data) :
    (⟨(freshFill (readReply errno committed range)).errno,
      filled (freshFill (readReply errno committed range))⟩ : ReadResult) =
      readResult errno committed := by
  by_cases zero : errno = 0
  · subst zero
    have bound := fresh_le size (first rfl)
    have copy : Bytes.build committed.size
        (fun i => ((Bytes.build 4096 fun _ => 0).splice 0 range).get i) = committed :=
      build_prefix (by change _ < 18446744073709551616; omega)
        (fresh_splice_prefix size (first rfl))
    simp only [freshFill_zero, readResult, ↓reduceIte, filled, copy]
  · simp only [freshFill, readReply, readResult, FillResult.of, zero, ↓reduceIte, filled]
    congr 1

/-- The step after the read of a step is the step after the bytes read. -/
theorem afterRead_fresh (state : BufferState Acc) {errno : UInt64} {committed range : Bytes}
    (size : range.data.size = (4096 : UInt64).toNat)
    (first : errno = 0 → range.data.extract 0 committed.data.size = committed.data) :
    afterRead state (freshFill (readReply errno committed range)) =
      afterBytes state (readResult errno committed) := by
  rw [← filled_fresh size first]
  simp only [afterRead, afterBytes, filled, Bytes.size_build]

theorem readStep_eq (state : BufferState Acc) :
    readStep state = .read 4096 fun reply => .pure (afterRead state (freshFill reply)) :=
  bind_readStdin_fresh _

structure Safe (state : BufferState Acc) : Prop where
  inputSize : state.input.data.size < UInt64.size
  cursor : state.cursor.toNat ≤ state.input.data.size
  outputSize : state.output.data.size < UInt64.size
  writing : (state.output.data.size = 0 ∧ state.written = 0) ∨
    state.written < state.output.size

theorem Safe.initial (seed : Acc) : Safe (initial seed) := by
  refine ⟨by change 0 < UInt64.size; decide, by change 0 ≤ 0; decide,
    by change 0 < UInt64.size; decide, Or.inl ⟨rfl, rfl⟩⟩

theorem Safe.input_toNat {state : BufferState Acc} (safe : Safe state) :
    state.input.size.toNat = state.input.data.size :=
  Bytes.size_toNat state.input safe.inputSize

theorem Safe.output_toNat {state : BufferState Acc} (safe : Safe state) :
    state.output.size.toNat = state.output.data.size :=
  Bytes.size_toNat state.output safe.outputSize

theorem Safe.written_le {state : BufferState Acc} (safe : Safe state) :
    state.written.toNat ≤ state.output.data.size := by
  rcases safe.writing with ⟨empty, zero⟩ | pending
  · simp only [empty, zero, UInt64.toNat_zero, Nat.le_refl]
  · have less := UInt64.lt_iff_toNat_lt.mp pending
    rw [safe.output_toNat] at less
    omega

theorem Safe.no_output {state : BufferState Acc} (safe : Safe state)
    (finished : ¬ state.written < state.output.size) :
    state.output.data.size = 0 ∧ state.written = 0 := by
  rcases safe.writing with empty | pending
  · exact empty
  · exact False.elim (finished pending)

theorem completeLine_safe (spec : KernelSpec kernel) {state : BufferState Acc} (safe : Safe state) :
    Safe (completeLine kernel state).state := by
  cases accepted : (kernel state.total state.line).valid with
  | false =>
      simpa only [completeLine, accepted, Bool.not_false, ↓reduceIte] using safe
  | true =>
      have bound := spec.outputBound state.total state.line accepted
      simp only [completeLine, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine ⟨safe.inputSize, safe.cursor, bound, ?_⟩
      by_cases empty : (kernel state.total state.line).output.data.size = 0
      · exact Or.inl ⟨empty, rfl⟩
      · apply Or.inr
        apply UInt64.lt_iff_toNat_lt.mpr
        rw [UInt64.toNat_zero, Bytes.size_toNat _ bound]
        omega

theorem completeLine_input (state : BufferState Acc) : ((completeLine kernel) state).state.input = state.input := by
  dsimp only [completeLine]
  split <;> rfl

theorem completeLine_cursor (state : BufferState Acc) : ((completeLine kernel) state).state.cursor = state.cursor := by
  dsimp only [completeLine]
  split <;> rfl

theorem completeLine_eof (state : BufferState Acc) : ((completeLine kernel) state).state.eof = state.eof := by
  dsimp only [completeLine]
  split <;> rfl

theorem completeLine_stopped (state : BufferState Acc) (stopped : ((completeLine kernel) state).running = false) :
    ((completeLine kernel) state).status = 28 := by
  dsimp only [completeLine] at stopped ⊢
  split <;> simp_all

theorem consumeStep_safe (spec : KernelSpec kernel) {current : ProcessStep (BufferState Acc)}
    (safe : Safe current.state)
    (test : consumeTest current = true) :
    Safe ((consumeStep kernel) current).state ∧
      ((consumeStep kernel) current).state.input = current.state.input ∧
      ((consumeStep kernel) current).state.eof = current.state.eof ∧
      current.state.cursor.toNat < ((consumeStep kernel) current).state.cursor.toNat := by
  have cursorLt : current.state.cursor < current.state.input.size := by
    simp only [consumeTest, Bool.and_eq_true, decide_eq_true_eq] at test
    exact test.2
  have cursorNat := UInt64.lt_iff_toNat_lt.mp cursorLt
  rw [safe.input_toNat] at cursorNat
  have nextNat : (current.state.cursor + 1).toNat = current.state.cursor.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (by omega) safe.inputSize
  have nextSafe : Safe { current.state with cursor := current.state.cursor + 1 } :=
    ⟨safe.inputSize, by simpa only [nextNat] using Nat.succ_le_of_lt cursorNat,
      safe.outputSize, safe.writing⟩
  dsimp only [consumeStep]
  split
  · exact ⟨completeLine_safe spec nextSafe, completeLine_input (kernel := kernel) _, completeLine_eof (kernel := kernel) _,
      by rw [completeLine_cursor, nextNat]; omega⟩
  · exact ⟨⟨nextSafe.inputSize, nextSafe.cursor, nextSafe.outputSize, nextSafe.writing⟩,
      rfl, rfl, by rw [nextNat]; omega⟩

theorem consumeStep_stopped (current : ProcessStep (BufferState Acc))
    (stopped : ((consumeStep kernel) current).running = false) : ((consumeStep kernel) current).status = 28 := by
  dsimp only [consumeStep] at stopped ⊢
  split at stopped
  · rename_i newline
    simpa only [newline, ↓reduceIte] using completeLine_stopped _ stopped
  · exact Bool.noConfusion stopped

theorem consumeGo_safe (spec : KernelSpec kernel) (fuel : Nat)
    (current : ProcessStep (BufferState Acc)) (safe : Safe current.state) :
    let result := LeanExe.repeatWhile.go consumeTest (consumeStep kernel) fuel current
    Safe result.state ∧ result.state.input = current.state.input ∧
      result.state.eof = current.state.eof ∧ current.state.cursor.toNat ≤ result.state.cursor.toNat := by
  induction fuel generalizing current with
  | zero => exact ⟨safe, rfl, rfl, Nat.le_refl _⟩
  | succ fuel ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · rename_i test
        obtain ⟨nextSafe, inputEq, eofEq, cursorLt⟩ := consumeStep_safe spec safe test
        obtain ⟨finalSafe, finalInput, finalEof, cursorLe⟩ := ih _ nextSafe
        exact ⟨finalSafe, finalInput.trans inputEq, finalEof.trans eofEq, by omega⟩
      · exact ⟨safe, rfl, rfl, Nat.le_refl _⟩

theorem consumeGo_stopped (fuel : Nat) (current : ProcessStep (BufferState Acc))
    (initialStatus : current.running = false → current.status = 28) :
    let result := LeanExe.repeatWhile.go consumeTest (consumeStep kernel) fuel current
    result.running = false → result.status = 28 := by
  induction fuel generalizing current with
  | zero => exact initialStatus
  | succ fuel ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · exact ih _ (consumeStep_stopped current)
      · exact initialStatus

theorem consumeInput_safe (spec : KernelSpec kernel) {state : BufferState Acc} (safe : Safe state) :
    Safe ((consumeInput kernel) state).state ∧ ((consumeInput kernel) state).state.input = state.input ∧
      ((consumeInput kernel) state).state.eof = state.eof := by
  have result := consumeGo_safe spec (state.input.size - state.cursor).toNat
    (ProcessStep.mk true 0 state) safe
  exact ⟨result.1, result.2.1, result.2.2.1⟩

theorem consumeInput_cursor (spec : KernelSpec kernel) {state : BufferState Acc} (safe : Safe state)
    (empty : state.output.size = 0) (remaining : state.cursor < state.input.size) :
    state.cursor.toNat < ((consumeInput kernel) state).state.cursor.toNat := by
  have remainingNat := UInt64.lt_iff_toNat_lt.mp remaining
  have countNat : 0 < (state.input.size - state.cursor).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega
  obtain ⟨fuel, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt countNat)
  have test : consumeTest (ProcessStep.mk true 0 state) = true := by
    simp [consumeTest, empty, remaining]
  have first := consumeStep_safe spec safe test
  have rest := consumeGo_safe spec fuel ((consumeStep kernel) (ProcessStep.mk true 0 state)) first.1
  change state.cursor.toNat <
    (LeanExe.repeatWhile.go consumeTest (consumeStep kernel) (state.input.size - state.cursor).toNat
      (ProcessStep.mk true 0 state)).state.cursor.toNat
  rw [countEq, LeanExe.repeatWhile.go]
  simpa only [test, ↓reduceIte] using Nat.lt_of_lt_of_le first.2.2.2 rest.2.2.2

theorem consumeInput_stopped (state : BufferState Acc) (stopped : ((consumeInput kernel) state).running = false) :
    ((consumeInput kernel) state).status = 28 :=
  consumeGo_stopped (state.input.size - state.cursor).toNat (ProcessStep.mk true 0 state)
    (by simp) stopped

theorem remainingOutput_size {state : BufferState Acc} (safe : Safe state) :
    (remainingOutput state).data.size = state.output.data.size - state.written.toNat :=
  state.output.range_from_size safe.outputSize safe.written_le

theorem afterBytes_safe {state : BufferState Acc} (safe : Safe state) (bytes : Bytes)
    (bound : bytes.data.size ≤ 4096) : Safe (afterBytes state ⟨0, bytes⟩).state := by
  simp only [afterBytes, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by change bytes.data.size < 18446744073709551616; omega,
    by simp, safe.outputSize, safe.writing⟩

theorem afterWrite_safe {state : BufferState Acc} (safe : Safe state) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput state).data.size) :
    Safe (afterWrite state ⟨0, count⟩).state := by
  rw [remainingOutput_size safe] at bound
  have sumBound : state.written.toNat + count.toNat ≤ state.output.data.size := by
    have writtenLe := safe.written_le
    omega
  have sumNat : (state.written + count).toNat = state.written.toNat + count.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt sumBound safe.outputSize)]
  simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨safe.inputSize, safe.cursor, by change 0 < UInt64.size; decide, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i different
    simp only [beq_iff_eq] at different
    refine ⟨safe.inputSize, safe.cursor, safe.outputSize, Or.inr ?_⟩
    apply UInt64.lt_iff_toNat_lt.mpr
    have differentNat : (state.written + count).toNat ≠ state.output.size.toNat := by
      intro equal
      exact different (UInt64.toNat_inj.mp equal)
    rw [sumNat, safe.output_toNat] at differentNat ⊢
    omega

end Demos.StreamFold
