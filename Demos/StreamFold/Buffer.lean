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

theorem model_head_success (state : (Model.State Acc)) (byte : UInt64) (rest : List UInt64)
    (final : (Model.State Acc)) (success : (Model.consume kernel) state (byte :: rest) = .ok final) :
    ∃ middle, (Model.consumeByte kernel) state byte = .ok middle ∧
      (Model.consume kernel) middle rest = .ok final := by
  rw [Model.consume_cons] at success
  cases first : (Model.consumeByte kernel) state byte with
  | error code => simp [first, bind, Except.bind] at success
  | ok middle => exact ⟨middle, rfl, by simpa [first, bind, Except.bind] using success⟩

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

structure BufferProgress (state : (BufferState Acc)) (history : List Bytes) (final : (Model.State Acc))
    (result : ProcessStep (BufferState Acc)) (consumed : List UInt64) : Prop where
  running : result.running = true
  status : result.status = 0
  safe : Safe result.state
  input : result.state.input = state.input
  eof : result.state.eof = state.eof
  cursor : result.state.cursor.toNat = state.cursor.toNat + consumed.length
  normal : spec.Good result.state.total
  split : unreadWords state = consumed ++ unreadWords result.state
  consumed : (Model.consume kernel) (bufferModel state history) consumed =
    .ok (bufferModel result.state (history ++ bufferOutputs result.state))
  continuation : (Model.consume kernel) (bufferModel result.state (history ++ bufferOutputs result.state))
    (unreadWords result.state) = .ok final
  modelSafe : Model.Safe spec (bufferModel result.state (history ++ bufferOutputs result.state))
    (unreadWords result.state)

theorem consumeGo_buffer (fuel : Nat) (state : (BufferState Acc)) (history : List Bytes) (final : (Model.State Acc))
    (safe : Safe state) (empty : state.output.size = 0) (normal : spec.Good state.total)
    (modelSafe : Model.Safe spec (bufferModel state history) (unreadWords state))
    (success : (Model.consume kernel) (bufferModel state history) (unreadWords state) = .ok final) :
    ∃ consumed, BufferProgress spec state history final
      (LeanExe.repeatWhile.go consumeTest (consumeStep kernel) fuel ⟨true, 0, state⟩)
      consumed := by
  induction fuel generalizing state history final with
  | zero =>
      change ∃ consumed, BufferProgress spec state history final (⟨true, 0, state⟩) consumed
      refine ⟨[], ⟨rfl, rfl, safe, rfl, rfl, by simp, normal, by simp, ?_, ?_, ?_⟩⟩
      · simp [bufferOutputs_empty safe empty, bufferModel]
      · simpa only [bufferOutputs_empty safe empty, List.append_nil] using success
      · simpa only [bufferOutputs_empty safe empty, List.append_nil] using modelSafe
  | succ fuel ih =>
      by_cases remaining : state.cursor < state.input.size
      · have test : consumeTest (ProcessStep.mk true 0 state) = true := by
          simp [consumeTest, empty, remaining]
        have oldWords := unreadWords_cons safe remaining
        let byte := state.input.get state.cursor
        let tail := (byteWords state.input).drop (state.cursor.toNat + 1)
        have words : unreadWords state = byte :: tail := oldWords
        rw [words] at success modelSafe
        obtain ⟨middle, first, rest⟩ := model_head_success _ byte tail final success
        have increment := cursor_increment safe remaining
        have stepFacts := consumeStep_safe spec safe test
        by_cases newline : byte = 10
        · have parsed : (kernel state.total state.line).valid = true := by
            cases accepted : (kernel state.total state.line).valid with
            | true => rfl
            | false =>
                simp [newline, Model.consumeByte, Model.emitLine, bufferModel, accepted] at first
          let advanced : (BufferState Acc) := { state with cursor := state.cursor + 1 }
          let next := (completeLine kernel) advanced
          have normalNext := completeLine_buffer spec advanced history normal (modelSafe.1 newline) parsed
          have nextEq : (consumeStep kernel) (ProcessStep.mk true 0 state) = next := by
            simp only [consumeStep, byte, newline, beq_self_eq_true, ↓reduceIte, next, advanced]
          have nextSafe : Safe next.state := by simpa only [nextEq] using stepFacts.1
          have nextInput : next.state.input = state.input := completeLine_input advanced
          have nextEof : next.state.eof = state.eof := completeLine_eof advanced
          have nextCursor : next.state.cursor.toNat = state.cursor.toNat + 1 := by
            simpa only [next, completeLine_cursor, advanced] using increment
          have nextUnread : unreadWords next.state = tail := by
            simp only [unreadWords, nextInput, nextCursor, tail]
          have outputPositive : 0 < next.state.output.data.size := normalNext.2.2.2.1
          have output : bufferOutputs next.state = [next.state.output] := by
            simp only [bufferOutputs, Nat.ne_of_gt outputPositive, ↓reduceIte]
          have firstNext : (Model.consumeByte kernel) (bufferModel state history) byte =
              .ok (bufferModel next.state (history ++ bufferOutputs next.state)) := by
            rw [output, newline]
            simpa only [bufferModel, advanced, next] using normalNext.2.2.2.2
          have middleEq : middle = bufferModel next.state (history ++ bufferOutputs next.state) :=
            Except.ok.inj (first.symm.trans firstNext)
          have nextStop : consumeTest next = false := by
            have outputWord : next.state.output.size ≠ 0 := by
              intro zero
              have := congrArg UInt64.toNat zero
              rw [nextSafe.output_toNat, UInt64.toNat_zero] at this
              omega
            simp [consumeTest, outputWord]
          refine ⟨[byte], ?_⟩
          simp only [LeanExe.repeatWhile.go, test, ↓reduceIte, nextEq, consumeGo_stop fuel next nextStop]
          refine ⟨normalNext.1, normalNext.2.1, nextSafe, nextInput, nextEof,
            by simpa using nextCursor, normalNext.2.2.1, ?_, ?_, ?_, ?_⟩
          · simpa only [nextUnread, List.singleton_append] using words
          · simp [Model.consume_cons, firstNext, bind, Except.bind]
          · simpa only [middleEq, nextUnread] using rest
          · simpa only [nextUnread] using modelSafe.2 _ firstNext
        · let next : (BufferState Acc) := { state with cursor := state.cursor + 1, line := state.line.push byte }
          have nextEq : (consumeStep kernel) (ProcessStep.mk true 0 state) = ⟨true, 0, next⟩ := by
            simp [consumeStep, byte, newline, next]
          have nextSafe : Safe next := by simpa only [nextEq] using stepFacts.1
          have nextUnread : unreadWords next = tail := by
            simp only [unreadWords, next, increment, tail]
          have firstNext : (Model.consumeByte kernel) (bufferModel state history) byte =
              .ok (bufferModel next history) := by
            simp [Model.consumeByte, bufferModel, next, newline]
          have middleEq : middle = bufferModel next history := Except.ok.inj (first.symm.trans firstNext)
          have nextModelSafe : Model.Safe spec (bufferModel next history) (unreadWords next) := by
            simpa only [nextUnread] using modelSafe.2 _ firstNext
          have nextSuccess : (Model.consume kernel) (bufferModel next history) (unreadWords next) = .ok final := by
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
          · rw [Model.consume_cons, firstNext]
            simpa [bind, Except.bind] using progress.consumed
      · have test : consumeTest (ProcessStep.mk true 0 state) = false := by
          simp [consumeTest, empty, remaining]
        refine ⟨[], ?_⟩
        simp only [LeanExe.repeatWhile.go, test, Bool.false_eq_true, ↓reduceIte]
        refine ⟨rfl, rfl, safe, rfl, rfl, by simp, normal, by simp, ?_, ?_, ?_⟩
        · simp [bufferOutputs_empty safe empty, bufferModel]
        · simpa only [bufferOutputs_empty safe empty, List.append_nil] using success
        · simpa only [bufferOutputs_empty safe empty, List.append_nil] using modelSafe

theorem consumeInput_buffer (state : (BufferState Acc)) (history : List Bytes) (final : (Model.State Acc))
    (safe : Safe state) (empty : state.output.size = 0) (normal : spec.Good state.total)
    (modelSafe : Model.Safe spec (bufferModel state history) (unreadWords state))
    (success : (Model.consume kernel) (bufferModel state history) (unreadWords state) = .ok final) :
    BufferProgress spec state history final ((consumeInput kernel) state)
      ((unreadWords state).take (((consumeInput kernel) state).state.cursor.toNat - state.cursor.toNat)) := by
  obtain ⟨consumed, progress⟩ := consumeGo_buffer spec (state.input.size - state.cursor).toNat
    state history final safe empty normal modelSafe success
  change BufferProgress spec state history final ((consumeInput kernel) state) consumed at progress
  have cursor : ((consumeInput kernel) state).state.cursor.toNat = state.cursor.toNat + consumed.length :=
    progress.cursor
  have length : ((consumeInput kernel) state).state.cursor.toNat - state.cursor.toNat = consumed.length := by
    omega
  have taken : (unreadWords state).take consumed.length = consumed := by
    rw [progress.split, List.take_append_length]
  simpa only [length, taken] using progress

end Demos.StreamFold

