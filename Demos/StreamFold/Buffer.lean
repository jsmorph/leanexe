import Demos.StreamFold.Bytes
import Demos.StreamFold.Model

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

variable {Acc : Type} {kernel : Kernel Acc} (spec : KernelSpec kernel)

def bufferModel (state : (BufferState Acc)) (history : List Bytes) : (Model.State Acc) :=
  ⟨state.total, state.line, history⟩

def bufferOutputs (state : (BufferState Acc)) : List Bytes :=
  if state.output.data.size = 0 then [] else [state.output]

def unreadWords (state : (BufferState Acc)) : List UInt64 :=
  (byteWords state.input).drop state.cursor.toNat

theorem bufferOutputs_empty {state : (BufferState Acc)} (safe : Safe state)
    (empty : state.output.size = 0) : bufferOutputs state = [] := by
  have same := congrArg UInt64.toNat empty
  rw [safe.output_toNat, UInt64.toNat_zero] at same
  simp [bufferOutputs, same]

theorem unreadWords_cons {state : (BufferState Acc)} (safe : Safe state)
    (remaining : state.cursor < state.input.size) :
    unreadWords state = state.input.get state.cursor ::
      (byteWords state.input).drop (state.cursor.toNat + 1) := by
  have inside : state.cursor.toNat < state.input.data.size := by
    have := UInt64.lt_iff_toNat_lt.mp remaining
    simpa only [safe.input_toNat] using this
  rw [unreadWords, List.drop_eq_getElem_cons (by simpa using inside), byteWords_get state.input _ inside]

theorem cursor_increment {state : (BufferState Acc)} (safe : Safe state)
    (remaining : state.cursor < state.input.size) :
    (state.cursor + 1).toNat = state.cursor.toNat + 1 := by
  have inside := UInt64.lt_iff_toNat_lt.mp remaining
  rw [safe.input_toNat] at inside
  rw [UInt64.toNat_add, UInt64.toNat_one]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) safe.inputSize)

theorem consumeGo_stop (fuel : Nat) (current : ProcessStep (BufferState Acc))
    (stopped : consumeTest current = false) :
    LeanExe.repeatWhile.go consumeTest (consumeStep kernel) fuel current = current := by
  cases fuel <;> simp [LeanExe.repeatWhile.go, stopped]

theorem completeLine_buffer (state : BufferState Acc) (history : List Bytes)
    (normal : spec.Good state.total) (room : spec.Room state.total state.line)
    (accepted : (kernel state.total state.line).valid = true) :
    (completeLine kernel state).running = true ∧ (completeLine kernel state).status = 0 ∧
      spec.Good (completeLine kernel state).state.total ∧
      0 < (completeLine kernel state).state.output.data.size ∧
      Model.consumeByte kernel (bufferModel state history) 10 =
        .ok (bufferModel (completeLine kernel state).state
          (history ++ [(completeLine kernel state).state.output])) := by
  obtain ⟨normalNext, outputPositive⟩ := spec.accepted normal room accepted
  refine ⟨by simp [completeLine, accepted], by simp [completeLine, accepted], ?_, ?_, ?_⟩
  · simpa only [completeLine, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using normalNext
  · simpa only [completeLine, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using outputPositive
  · simp [Model.consumeByte, Model.emitLine, bufferModel, completeLine, accepted]

structure BufferProgress (state : BufferState Acc) (history : List Bytes)
    (result : ProcessStep (BufferState Acc)) (consumed : List UInt64) : Prop where
  safe : Safe result.state
  input : result.state.input = state.input
  eof : result.state.eof = state.eof
  cursor : result.state.cursor.toNat = state.cursor.toNat + consumed.length
  split : unreadWords state = consumed ++ unreadWords result.state
  running : result.running = true → result.status = 0 ∧ spec.Good result.state.total ∧
    Model.consume kernel (bufferModel state history) consumed =
      .ok (bufferModel result.state (history ++ bufferOutputs result.state))
  stopped : result.running = false → result.status = 28 ∧
    Model.consume kernel (bufferModel state history) consumed =
      .error (bufferModel result.state history)

theorem BufferProgress.unmoved {state : BufferState Acc} {history : List Bytes} (safe : Safe state)
    (empty : state.output.size = 0) (normal : spec.Good state.total) :
    BufferProgress spec state history ⟨true, 0, state⟩ [] := by
  refine ⟨safe, rfl, rfl, by simp, by simp, fun _ => ⟨rfl, normal, ?_⟩, fun stopped => nomatch stopped⟩
  simp [bufferOutputs_empty safe empty, bufferModel]

theorem consumeGo_buffer (fuel : Nat) (state : BufferState Acc) (history : List Bytes)
    (safe : Safe state) (empty : state.output.size = 0) (normal : spec.Good state.total)
    (modelSafe : Model.Safe spec (bufferModel state history) (unreadWords state)) :
    ∃ consumed, BufferProgress spec state history
      (LeanExe.repeatWhile.go consumeTest (consumeStep kernel) fuel ⟨true, 0, state⟩)
      consumed := by
  induction fuel generalizing state history with
  | zero => exact ⟨[], BufferProgress.unmoved spec safe empty normal⟩
  | succ fuel ih =>
      by_cases remaining : state.cursor < state.input.size
      · have test : consumeTest (ProcessStep.mk true 0 state) = true := by
          simp [consumeTest, empty, remaining]
        have oldWords := unreadWords_cons safe remaining
        let byte := state.input.get state.cursor
        let tail := (byteWords state.input).drop (state.cursor.toNat + 1)
        have words : unreadWords state = byte :: tail := oldWords
        rw [words] at modelSafe
        have increment := cursor_increment safe remaining
        have stepFacts := consumeStep_safe spec safe test
        by_cases newline : byte = 10
        · let advanced : BufferState Acc := { state with cursor := state.cursor + 1 }
          let next := completeLine kernel advanced
          have nextEq : consumeStep kernel (ProcessStep.mk true 0 state) = next := by
            simp only [consumeStep, byte, newline, beq_self_eq_true, ↓reduceIte, next, advanced]
          have nextSafe : Safe next.state := by simpa only [nextEq] using stepFacts.1
          have nextInput : next.state.input = state.input := completeLine_input advanced
          have nextEof : next.state.eof = state.eof := completeLine_eof advanced
          have nextCursor : next.state.cursor.toNat = state.cursor.toNat + 1 := by
            simpa only [next, completeLine_cursor, advanced] using increment
          have nextUnread : unreadWords next.state = tail := by
            simp only [unreadWords, nextInput, nextCursor, tail]
          have split : unreadWords state = [byte] ++ unreadWords next.state := by
            simpa only [nextUnread, List.singleton_append] using words
          cases parsed : (kernel state.total state.line).valid with
          | false =>
              have stoppedEq : next = ⟨false, 28, advanced⟩ := by
                simp [next, completeLine, advanced, parsed]
              have nextStop : consumeTest next = false := by simp [consumeTest, stoppedEq]
              refine ⟨[byte], ?_⟩
              simp only [LeanExe.repeatWhile.go, test, ↓reduceIte, nextEq,
                consumeGo_stop fuel next nextStop]
              refine ⟨nextSafe, nextInput, nextEof, by simpa using nextCursor, split, ?_, ?_⟩
              · intro running
                simp [stoppedEq] at running
              · intro _
                refine ⟨by simp [stoppedEq], ?_⟩
                simp [Model.consume_cons, Model.consumeByte, Model.emitLine, bufferModel, newline,
                  parsed, stoppedEq, advanced, bind, Except.bind]
          | true =>
              have normalNext := completeLine_buffer spec advanced history normal
                (modelSafe.1 newline) parsed
              have outputPositive : 0 < next.state.output.data.size := normalNext.2.2.2.1
              have output : bufferOutputs next.state = [next.state.output] := by
                simp only [bufferOutputs, Nat.ne_of_gt outputPositive, ↓reduceIte]
              have firstNext : Model.consumeByte kernel (bufferModel state history) byte =
                  .ok (bufferModel next.state (history ++ bufferOutputs next.state)) := by
                rw [output, newline]
                simpa only [bufferModel, advanced, next] using normalNext.2.2.2.2
              have nextStop : consumeTest next = false := by
                have outputWord : next.state.output.size ≠ 0 := by
                  intro zero
                  have := congrArg UInt64.toNat zero
                  rw [nextSafe.output_toNat, UInt64.toNat_zero] at this
                  omega
                simp [consumeTest, outputWord]
              refine ⟨[byte], ?_⟩
              simp only [LeanExe.repeatWhile.go, test, ↓reduceIte, nextEq,
                consumeGo_stop fuel next nextStop]
              refine ⟨nextSafe, nextInput, nextEof, by simpa using nextCursor, split,
                fun _ => ⟨normalNext.2.1, normalNext.2.2.1, ?_⟩, ?_⟩
              · simp [Model.consume_cons, firstNext, bind, Except.bind]
              · intro stopped
                rw [normalNext.1] at stopped
                cases stopped
        · let next : BufferState Acc :=
            { state with cursor := state.cursor + 1, line := state.line.push byte }
          have nextEq : consumeStep kernel (ProcessStep.mk true 0 state) = ⟨true, 0, next⟩ := by
            simp [consumeStep, byte, newline, next]
          have nextSafe : Safe next := by simpa only [nextEq] using stepFacts.1
          have nextUnread : unreadWords next = tail := by
            simp only [unreadWords, next, increment, tail]
          have firstNext : Model.consumeByte kernel (bufferModel state history) byte =
              .ok (bufferModel next history) := by
            simp [Model.consumeByte, bufferModel, next, newline]
          have nextModelSafe : Model.Safe spec (bufferModel next history) (unreadWords next) := by
            simpa only [nextUnread] using modelSafe.2 _ firstNext
          obtain ⟨consumed, progress⟩ := ih next history nextSafe empty normal nextModelSafe
          have prepend : Model.consume kernel (bufferModel state history) (byte :: consumed) =
              Model.consume kernel (bufferModel next history) consumed := by
            rw [Model.consume_cons, firstNext]
            rfl
          refine ⟨byte :: consumed, ?_⟩
          simp only [LeanExe.repeatWhile.go, test, ↓reduceIte, nextEq]
          refine ⟨progress.safe, progress.input, progress.eof, ?_, ?_, ?_, ?_⟩
          · have nextCursor : next.cursor.toNat = state.cursor.toNat + 1 := increment
            rw [progress.cursor, nextCursor, List.length_cons]
            omega
          · rw [words, ← nextUnread, progress.split, List.cons_append]
          · intro running
            rw [prepend]
            exact progress.running running
          · intro stopped
            rw [prepend]
            exact progress.stopped stopped
      · have test : consumeTest (ProcessStep.mk true 0 state) = false := by
          simp [consumeTest, empty, remaining]
        refine ⟨[], ?_⟩
        simp only [LeanExe.repeatWhile.go, test, Bool.false_eq_true, ↓reduceIte]
        exact BufferProgress.unmoved spec safe empty normal

theorem consumeInput_buffer (state : BufferState Acc) (history : List Bytes)
    (safe : Safe state) (empty : state.output.size = 0) (normal : spec.Good state.total)
    (modelSafe : Model.Safe spec (bufferModel state history) (unreadWords state)) :
    ∃ consumed, BufferProgress spec state history (consumeInput kernel state) consumed :=
  consumeGo_buffer spec (state.input.size - state.cursor).toNat state history safe empty normal
    modelSafe

end Demos.StreamFold
