import Demos.RunningSum.StreamBytes
import Demos.RunningSum.StreamModel

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi

def bufferModel (state : State) (history : List Bytes) : StreamModel.State :=
  ⟨state.total, state.line, history⟩

def bufferOutputs (state : State) : List Bytes :=
  if state.output.data.size = 0 then [] else [state.output]

def unreadWords (state : State) : List UInt64 :=
  (byteWords state.input).drop state.cursor.toNat

theorem bufferOutputs_empty {state : State} (safe : Termination.Safe state)
    (empty : state.output.size = 0) : bufferOutputs state = [] := by
  have same := congrArg UInt64.toNat empty
  rw [safe.output_toNat, UInt64.toNat_zero] at same
  simp [bufferOutputs, same]

theorem unreadWords_cons {state : State} (safe : Termination.Safe state)
    (remaining : state.cursor < state.input.size) :
    unreadWords state = state.input.get state.cursor ::
      (byteWords state.input).drop (state.cursor.toNat + 1) := by
  have inside : state.cursor.toNat < state.input.data.size := by
    have := UInt64.lt_iff_toNat_lt.mp remaining
    simpa only [safe.input_toNat] using this
  rw [unreadWords, List.drop_eq_getElem_cons (by simpa using inside), byteWords_get state.input _ inside]

theorem cursor_increment {state : State} (safe : Termination.Safe state)
    (remaining : state.cursor < state.input.size) :
    (state.cursor + 1).toNat = state.cursor.toNat + 1 := by
  have inside := UInt64.lt_iff_toNat_lt.mp remaining
  rw [safe.input_toNat] at inside
  rw [UInt64.toNat_add, UInt64.toNat_one]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) safe.inputSize)

theorem consumeGo_stop (fuel : Nat) (current : ProcessStep State)
    (stopped : Termination.consumeTest current = false) :
    LeanExe.repeatWhile.go Termination.consumeTest Termination.consumeStep fuel current = current := by
  cases fuel <;> simp [LeanExe.repeatWhile.go, stopped]

theorem model_head_success (state : StreamModel.State) (byte : UInt64) (rest : List UInt64)
    (final : StreamModel.State) (success : StreamModel.consume state (byte :: rest) = .ok final) :
    ∃ middle, StreamModel.consumeByte state byte = .ok middle ∧
      StreamModel.consume middle rest = .ok final := by
  rw [StreamModel.consume_cons] at success
  cases first : StreamModel.consumeByte state byte with
  | error code => simp [first, bind, Except.bind] at success
  | ok middle => exact ⟨middle, rfl, by simpa [first, bind, Except.bind] using success⟩

theorem completeLine_buffer (state : State) (history : List Bytes)
    (normal : state.total.Valid) (room : StreamModel.Room (bufferModel state history))
    (accepted : (parse state.line).valid = true) :
    (completeLine state).running = true ∧ (completeLine state).status = 0 ∧
      (completeLine state).state.total.Valid ∧
      0 < (completeLine state).state.output.data.size ∧
      StreamModel.consumeByte (bufferModel state history) 10 =
        .ok (bufferModel (completeLine state).state (history ++ [(completeLine state).state.output])) := by
  change max state.total.digits.size state.line.size + 3 < UInt64.size at room
  have lineBound : state.line.size < UInt64.size := by
    omega
  have parsedNormal := parse_valid state.line lineBound accepted
  have parsedSize := parse_digits_size_le state.line lineBound
  have addBound : max state.total.digits.size (parse state.line).value.digits.size + 3 < UInt64.size := by
    omega
  obtain ⟨sumNormal, sumFits, _, _⟩ := add_correct state.total (parse state.line).value
    normal parsedNormal addBound
  refine ⟨by simp [completeLine, accepted], by simp [completeLine, accepted], ?_, ?_, ?_⟩
  · simpa only [completeLine, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using sumNormal
  · simpa only [completeLine, accepted, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using
      render_nonempty (add state.total (parse state.line).value) sumFits
  · simp [StreamModel.consumeByte, StreamModel.emitLine, bufferModel, completeLine, accepted]

structure BufferProgress (state : State) (history : List Bytes) (final : StreamModel.State)
    (result : ProcessStep State) (consumed : List UInt64) : Prop where
  running : result.running = true
  status : result.status = 0
  safe : Termination.Safe result.state
  input : result.state.input = state.input
  eof : result.state.eof = state.eof
  cursor : result.state.cursor.toNat = state.cursor.toNat + consumed.length
  normal : result.state.total.Valid
  split : unreadWords state = consumed ++ unreadWords result.state
  consumed : StreamModel.consume (bufferModel state history) consumed =
    .ok (bufferModel result.state (history ++ bufferOutputs result.state))
  continuation : StreamModel.consume (bufferModel result.state (history ++ bufferOutputs result.state))
    (unreadWords result.state) = .ok final
  modelSafe : StreamModel.Safe (bufferModel result.state (history ++ bufferOutputs result.state))
    (unreadWords result.state)

theorem consumeGo_buffer (fuel : Nat) (state : State) (history : List Bytes) (final : StreamModel.State)
    (safe : Termination.Safe state) (empty : state.output.size = 0) (normal : state.total.Valid)
    (modelSafe : StreamModel.Safe (bufferModel state history) (unreadWords state))
    (success : StreamModel.consume (bufferModel state history) (unreadWords state) = .ok final) :
    ∃ consumed, BufferProgress state history final
      (LeanExe.repeatWhile.go Termination.consumeTest Termination.consumeStep fuel ⟨true, 0, state⟩)
      consumed := by
  induction fuel generalizing state history final with
  | zero =>
      change ∃ consumed, BufferProgress state history final (⟨true, 0, state⟩) consumed
      refine ⟨[], ⟨rfl, rfl, safe, rfl, rfl, by simp, normal, by simp, ?_, ?_, ?_⟩⟩
      · simp [bufferOutputs_empty safe empty, bufferModel]
      · simpa only [bufferOutputs_empty safe empty, List.append_nil] using success
      · simpa only [bufferOutputs_empty safe empty, List.append_nil] using modelSafe
  | succ fuel ih =>
      by_cases remaining : state.cursor < state.input.size
      · have test : Termination.consumeTest (ProcessStep.mk true 0 state) = true := by
          simp [Termination.consumeTest, empty, remaining]
        have oldWords := unreadWords_cons safe remaining
        let byte := state.input.get state.cursor
        let tail := (byteWords state.input).drop (state.cursor.toNat + 1)
        have words : unreadWords state = byte :: tail := oldWords
        rw [words] at success modelSafe
        obtain ⟨middle, first, rest⟩ := model_head_success _ byte tail final success
        have increment := cursor_increment safe remaining
        have stepFacts := Termination.consumeStep_safe safe test
        by_cases newline : byte = 10
        · have parsed : (parse state.line).valid = true := by
            by_contra rejected
            have parseFalse : (parse state.line).valid = false := Bool.eq_false_iff.mpr rejected
            simp [newline, StreamModel.consumeByte, StreamModel.emitLine, bufferModel, parseFalse] at first
          let advanced : State := { state with cursor := state.cursor + 1 }
          let next := completeLine advanced
          have normalNext := completeLine_buffer advanced history normal (modelSafe.1 newline) parsed
          have nextEq : Termination.consumeStep (ProcessStep.mk true 0 state) = next := by
            simp only [Termination.consumeStep, byte, newline, beq_self_eq_true, ↓reduceIte, next, advanced]
          have nextSafe : Termination.Safe next.state := by simpa only [nextEq] using stepFacts.1
          have nextInput : next.state.input = state.input := Termination.completeLine_input advanced
          have nextEof : next.state.eof = state.eof := Termination.completeLine_eof advanced
          have nextCursor : next.state.cursor.toNat = state.cursor.toNat + 1 := by
            simpa only [next, Termination.completeLine_cursor, advanced] using increment
          have nextUnread : unreadWords next.state = tail := by
            simp only [unreadWords, nextInput, nextCursor, tail]
          have outputPositive : 0 < next.state.output.data.size := normalNext.2.2.2.1
          have output : bufferOutputs next.state = [next.state.output] := by
            simp only [bufferOutputs, Nat.ne_of_gt outputPositive, ↓reduceIte]
          have firstNext : StreamModel.consumeByte (bufferModel state history) byte =
              .ok (bufferModel next.state (history ++ bufferOutputs next.state)) := by
            rw [output, newline]
            simpa only [bufferModel, advanced, next] using normalNext.2.2.2.2
          have middleEq : middle = bufferModel next.state (history ++ bufferOutputs next.state) :=
            Except.ok.inj (first.symm.trans firstNext)
          have nextStop : Termination.consumeTest next = false := by
            have outputWord : next.state.output.size ≠ 0 := by
              intro zero
              have := congrArg UInt64.toNat zero
              rw [nextSafe.output_toNat, UInt64.toNat_zero] at this
              omega
            simp [Termination.consumeTest, outputWord]
          refine ⟨[byte], ?_⟩
          simp only [LeanExe.repeatWhile.go, test, ↓reduceIte, nextEq, consumeGo_stop fuel next nextStop]
          refine ⟨normalNext.1, normalNext.2.1, nextSafe, nextInput, nextEof,
            by simpa using nextCursor, normalNext.2.2.1, ?_, ?_, ?_, ?_⟩
          · simpa only [nextUnread, List.singleton_append] using words
          · simp [StreamModel.consume_cons, firstNext, bind, Except.bind]
          · simpa only [middleEq, nextUnread] using rest
          · simpa only [nextUnread] using modelSafe.2 _ firstNext
        · let next : State := { state with cursor := state.cursor + 1, line := state.line.push byte }
          have nextEq : Termination.consumeStep (ProcessStep.mk true 0 state) = ⟨true, 0, next⟩ := by
            simp [Termination.consumeStep, byte, newline, next]
          have nextSafe : Termination.Safe next := by simpa only [nextEq] using stepFacts.1
          have nextUnread : unreadWords next = tail := by
            simp only [unreadWords, next, increment, tail]
          have firstNext : StreamModel.consumeByte (bufferModel state history) byte =
              .ok (bufferModel next history) := by
            simp [StreamModel.consumeByte, bufferModel, next, newline]
          have middleEq : middle = bufferModel next history := Except.ok.inj (first.symm.trans firstNext)
          have nextModelSafe : StreamModel.Safe (bufferModel next history) (unreadWords next) := by
            simpa only [nextUnread] using modelSafe.2 _ firstNext
          have nextSuccess : StreamModel.consume (bufferModel next history) (unreadWords next) = .ok final := by
            simpa only [middleEq, nextUnread] using rest
          obtain ⟨consumed, progress⟩ := ih next history final nextSafe empty normal nextModelSafe nextSuccess
          refine ⟨byte :: consumed, ?_⟩
          simp only [LeanExe.repeatWhile.go, test, ↓reduceIte, nextEq]
          refine ⟨progress.running, progress.status, progress.safe, progress.input, progress.eof,
            ?_, progress.normal, ?_, ?_, progress.continuation, progress.modelSafe⟩
          · have nextCursor : next.cursor.toNat = state.cursor.toNat + 1 := increment
            rw [progress.cursor, nextCursor, List.length_cons]
            omega
          · rw [words, ← nextUnread, progress.split, List.cons_append]
          · rw [StreamModel.consume_cons, firstNext]
            simpa [bind, Except.bind] using progress.consumed
      · have test : Termination.consumeTest (ProcessStep.mk true 0 state) = false := by
          simp [Termination.consumeTest, empty, remaining]
        refine ⟨[], ?_⟩
        simp only [LeanExe.repeatWhile.go, test, Bool.false_eq_true, ↓reduceIte]
        refine ⟨rfl, rfl, safe, rfl, rfl, by simp, normal, by simp, ?_, ?_, ?_⟩
        · simp [bufferOutputs_empty safe empty, bufferModel]
        · simpa only [bufferOutputs_empty safe empty, List.append_nil] using success
        · simpa only [bufferOutputs_empty safe empty, List.append_nil] using modelSafe

theorem consumeInput_buffer (state : State) (history : List Bytes) (final : StreamModel.State)
    (safe : Termination.Safe state) (empty : state.output.size = 0) (normal : state.total.Valid)
    (modelSafe : StreamModel.Safe (bufferModel state history) (unreadWords state))
    (success : StreamModel.consume (bufferModel state history) (unreadWords state) = .ok final) :
    BufferProgress state history final (consumeInput state)
      ((unreadWords state).take ((consumeInput state).state.cursor.toNat - state.cursor.toNat)) := by
  obtain ⟨consumed, progress⟩ := consumeGo_buffer (state.input.size - state.cursor).toNat
    state history final safe empty normal modelSafe success
  change BufferProgress state history final (consumeInput state) consumed at progress
  have cursor : (consumeInput state).state.cursor.toNat = state.cursor.toNat + consumed.length :=
    progress.cursor
  have length : (consumeInput state).state.cursor.toNat - state.cursor.toNat = consumed.length := by
    omega
  have taken : (unreadWords state).take consumed.length = consumed := by
    rw [progress.split, List.take_append_length]
  simpa only [length, taken] using progress

end Demos.RunningSum
