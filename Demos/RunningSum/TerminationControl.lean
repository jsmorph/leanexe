import Demos.RunningSum.Stream

namespace Demos.RunningSum.Termination

open LeanExe LeanExe.Wasi

structure Safe (state : State) : Prop where
  inputSize : state.input.data.size < UInt64.size
  cursor : state.cursor.toNat ≤ state.input.data.size
  outputSize : state.output.data.size < UInt64.size
  writing : (state.output.data.size = 0 ∧ state.written = 0) ∨
    state.written < state.output.size

theorem Safe.initial : Safe initial := by
  refine ⟨by decide, by decide, by decide, Or.inl ⟨rfl, rfl⟩⟩

theorem Safe.input_toNat {state : State} (safe : Safe state) :
    state.input.size.toNat = state.input.data.size :=
  Bytes.size_toNat state.input safe.inputSize

theorem Safe.output_toNat {state : State} (safe : Safe state) :
    state.output.size.toNat = state.output.data.size :=
  Bytes.size_toNat state.output safe.outputSize

theorem Safe.written_le {state : State} (safe : Safe state) :
    state.written.toNat ≤ state.output.data.size := by
  rcases safe.writing with ⟨empty, zero⟩ | pending
  · simp only [empty, zero, UInt64.toNat_zero, Nat.le_refl]
  · have less := UInt64.lt_iff_toNat_lt.mp pending
    rw [safe.output_toNat] at less
    omega

theorem Safe.no_output {state : State} (safe : Safe state)
    (finished : ¬ state.written < state.output.size) :
    state.output.data.size = 0 ∧ state.written = 0 := by
  rcases safe.writing with empty | pending
  · exact empty
  · exact False.elim (finished pending)

theorem render_size_bound (number : Decimal) : (render number).data.size < UInt64.size := by
  unfold render
  split
  · decide
  · rw [Bytes.data_size_build]
    exact UInt64.toNat_lt_size _

theorem completeLine_safe {state : State} (safe : Safe state) :
    Safe (completeLine state).state := by
  dsimp only [completeLine]
  split
  · exact safe
  · refine ⟨safe.inputSize, safe.cursor, render_size_bound _, ?_⟩
    by_cases empty : (render (add state.total (parse state.line).value)).data.size = 0
    · exact Or.inl ⟨empty, rfl⟩
    · apply Or.inr
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [UInt64.toNat_zero, Bytes.size_toNat _ (render_size_bound _)]
      omega

theorem completeLine_input (state : State) : (completeLine state).state.input = state.input := by
  dsimp only [completeLine]
  split <;> rfl

theorem completeLine_cursor (state : State) : (completeLine state).state.cursor = state.cursor := by
  dsimp only [completeLine]
  split <;> rfl

theorem completeLine_eof (state : State) : (completeLine state).state.eof = state.eof := by
  dsimp only [completeLine]
  split <;> rfl

theorem completeLine_stopped (state : State) (stopped : (completeLine state).running = false) :
    (completeLine state).status = 28 := by
  dsimp only [completeLine] at stopped ⊢
  split <;> simp_all

def consumeTest (current : ProcessStep State) : Bool :=
  current.running && current.state.output.size == 0 &&
    current.state.cursor < current.state.input.size

def consumeStep (current : ProcessStep State) : ProcessStep State :=
  let byte := current.state.input.get current.state.cursor
  let next := { current.state with cursor := current.state.cursor + 1 }
  if byte == 10 then completeLine next
  else ⟨true, 0, { next with line := next.line.push byte }⟩

theorem consumeStep_safe {current : ProcessStep State} (safe : Safe current.state)
    (test : consumeTest current = true) :
    Safe (consumeStep current).state ∧
      (consumeStep current).state.input = current.state.input ∧
      (consumeStep current).state.eof = current.state.eof ∧
      current.state.cursor.toNat < (consumeStep current).state.cursor.toNat := by
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
  · exact ⟨completeLine_safe nextSafe, completeLine_input _, completeLine_eof _,
      by rw [completeLine_cursor, nextNat]; omega⟩
  · exact ⟨⟨nextSafe.inputSize, nextSafe.cursor, nextSafe.outputSize, nextSafe.writing⟩,
      rfl, rfl, by rw [nextNat]; omega⟩

theorem consumeStep_stopped (current : ProcessStep State)
    (stopped : (consumeStep current).running = false) : (consumeStep current).status = 28 := by
  dsimp only [consumeStep] at stopped ⊢
  split at stopped
  · rename_i newline
    simpa only [newline, ↓reduceIte] using completeLine_stopped _ stopped
  · exact Bool.noConfusion stopped

theorem consumeGo_safe (fuel : Nat) (current : ProcessStep State) (safe : Safe current.state) :
    let result := LeanExe.repeatWhile.go consumeTest consumeStep fuel current
    Safe result.state ∧ result.state.input = current.state.input ∧
      result.state.eof = current.state.eof ∧ current.state.cursor.toNat ≤ result.state.cursor.toNat := by
  induction fuel generalizing current with
  | zero => exact ⟨safe, rfl, rfl, Nat.le_refl _⟩
  | succ fuel ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · rename_i test
        obtain ⟨nextSafe, inputEq, eofEq, cursorLt⟩ := consumeStep_safe safe test
        obtain ⟨finalSafe, finalInput, finalEof, cursorLe⟩ := ih _ nextSafe
        exact ⟨finalSafe, finalInput.trans inputEq, finalEof.trans eofEq, by omega⟩
      · exact ⟨safe, rfl, rfl, Nat.le_refl _⟩

theorem consumeGo_stopped (fuel : Nat) (current : ProcessStep State)
    (initialStatus : current.running = false → current.status = 28) :
    let result := LeanExe.repeatWhile.go consumeTest consumeStep fuel current
    result.running = false → result.status = 28 := by
  induction fuel generalizing current with
  | zero => exact initialStatus
  | succ fuel ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · exact ih _ (consumeStep_stopped current)
      · exact initialStatus

theorem consumeInput_safe {state : State} (safe : Safe state) :
    Safe (consumeInput state).state ∧ (consumeInput state).state.input = state.input ∧
      (consumeInput state).state.eof = state.eof := by
  have result := consumeGo_safe (state.input.size - state.cursor).toNat
    (ProcessStep.mk true 0 state) safe
  exact ⟨result.1, result.2.1, result.2.2.1⟩

theorem consumeInput_cursor {state : State} (safe : Safe state)
    (empty : state.output.size = 0) (remaining : state.cursor < state.input.size) :
    state.cursor.toNat < (consumeInput state).state.cursor.toNat := by
  have remainingNat := UInt64.lt_iff_toNat_lt.mp remaining
  have countNat : 0 < (state.input.size - state.cursor).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega
  obtain ⟨fuel, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt countNat)
  have test : consumeTest (ProcessStep.mk true 0 state) = true := by
    simp [consumeTest, empty, remaining]
  have first := consumeStep_safe safe test
  have rest := consumeGo_safe fuel (consumeStep (ProcessStep.mk true 0 state)) first.1
  change state.cursor.toNat <
    (LeanExe.repeatWhile.go consumeTest consumeStep (state.input.size - state.cursor).toNat
      (ProcessStep.mk true 0 state)).state.cursor.toNat
  rw [countEq, LeanExe.repeatWhile.go]
  simpa only [test, ↓reduceIte] using Nat.lt_of_lt_of_le first.2.2.2 rest.2.2.2

theorem consumeInput_stopped (state : State) (stopped : (consumeInput state).running = false) :
    (consumeInput state).status = 28 :=
  consumeGo_stopped (state.input.size - state.cursor).toNat (ProcessStep.mk true 0 state)
    (by simp) stopped

theorem remainingOutput_size {state : State} (safe : Safe state) :
    (remainingOutput state).data.size = state.output.data.size - state.written.toNat := by
  unfold remainingOutput
  rw [Bytes.data_size_build, UInt64.toNat_sub_of_le]
  · rw [safe.output_toNat]
  · exact UInt64.le_iff_toNat_le.mpr (by rw [safe.output_toNat]; exact safe.written_le)

theorem afterRead_safe {state : State} (safe : Safe state) (bytes : Bytes)
    (bound : bytes.data.size ≤ 4096) : Safe (afterRead state ⟨0, bytes⟩).state := by
  simp only [afterRead, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by change bytes.data.size < 18446744073709551616; omega,
    by simp, safe.outputSize, safe.writing⟩

theorem afterWrite_safe {state : State} (safe : Safe state) (count : UInt64)
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

end Demos.RunningSum.Termination
