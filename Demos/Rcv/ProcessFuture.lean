import Demos.Rcv.ProcessControl
import Demos.Rcv.TabulateBound

/-! The invariant of [the process](Process.lean) and its preservation by each step.  `Future`
relates a reached state to the input of the whole run.  Before EOF the input is the bytes held
followed by the unread input, and nothing has been written.  After EOF the input is read, and the
output written so far followed by the output that remains is the report of the input.
`future_step` states that each step keeps the invariant and that the stopping step returns status 0
after writing the report. -/

namespace Demos.Rcv.Process

open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition StreamHost byteWords byteWords_length)

/-- The bytes of the input words, each a byte. -/
def inputBytes (input : List UInt64) : List UInt8 := input.map UInt64.toUInt8

/-- The stdout bytes for the input bytes `input`: the report of the file `input`, the
requirements' `report b`. -/
def expectedOutput (input : List UInt64) : List UInt64 :=
  (Spec.reportFile (inputBytes input)).map UInt8.toUInt64

/-- The most bytes of a report, by `TabulateProgram.reportFile_length_le`. -/
def outputLimit : Nat := 1301030

/-- The invariant of a reached state `s` at stream position `position`, for the input bytes
`input` of the whole run. -/
structure Future (input : List UInt64) (s : State) (position : StreamPosition) : Prop where
  reading : s.eof = false → input = byteWords s.input ++ position.input ∧
    position.output = [] ∧ s.output.data.size = 0 ∧ s.written = 0
  ended : s.eof = true → position.input = [] ∧ s.input.data.size = 0 ∧
    position.output ++ byteWords (remainingOutput s) = expectedOutput input
  safe : Safe s
  inputSize : s.input.data.size ≤ input.length
  outputSize : s.output.data.size ≤ outputLimit

theorem future_initial (position : StreamPosition) (empty : position.output = []) :
    Future position.input initial position := by
  refine ⟨fun _ => ⟨by rw [show initial.input = Bytes.empty from rfl,
      Demos.StreamFold.byteWords_empty]; rfl, empty, rfl, rfl⟩,
    (fun impossible => by cases impossible), Safe.initial, Nat.zero_le _, Nat.zero_le _⟩

/-- A write happens only after EOF, and it keeps the invariant. -/
theorem future_afterWrite {input : List UInt64} {s : State} {position next : StreamPosition}
    (future : Future input s position) (pending : s.written < s.output.size)
    (count : UInt64) (bound : count.toNat ≤ (remainingOutput s).data.size)
    (sameInput : next.input = position.input)
    (output : next.output = position.output ++ (byteWords (remainingOutput s)).take count.toNat) :
    Future input (afterWrite s ⟨0, count⟩).state next := by
  have ended : s.eof = true := by
    cases eof : s.eof with
    | true => rfl
    | false =>
        obtain ⟨_, _, empty, _⟩ := future.reading eof
        have := UInt64.lt_iff_toNat_lt.mp pending
        rw [future.safe.output_toNat, empty] at this
        omega
  obtain ⟨sameIn, sameEof⟩ := afterWrite_fields s ⟨0, count⟩
  obtain ⟨noInput, inputEmpty, written⟩ := future.ended ended
  refine ⟨(fun impossible => by rw [sameEof, ended] at impossible; cases impossible),
    fun _ => ⟨by rw [sameInput, noInput], by rw [sameIn, inputEmpty], ?_⟩,
    afterWrite_safe future.safe count bound, by rw [sameIn]; exact future.inputSize,
    Nat.le_trans (afterWrite_output_le s _) future.outputSize⟩
  rw [output, afterWrite_conservation future.safe count bound, written]

/-- A read of nonempty bytes before EOF appends them to the input. -/
theorem future_read {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {position next : StreamPosition}
    (future : Future input s position) (reading : s.eof = false) (bytes : Bytes)
    (nonempty : bytes.data.size ≠ 0) (consumed : position.input = byteWords bytes ++ next.input)
    (sameOutput : next.output = position.output) :
    Future input (afterRead s ⟨0, bytes⟩).state next := by
  obtain ⟨split, written, outputEmpty, writtenZero⟩ := future.reading reading
  have total : s.input.data.size + bytes.data.size ≤ input.length := by
    have := congrArg List.length split
    rw [consumed] at this
    simp only [List.length_append, byteWords_length] at this
    omega
  have bytesNat : bytes.size.toNat = bytes.data.size := Bytes.size_toNat bytes (by omega)
  have test : (bytes.size == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro zero
    rw [zero, UInt64.toNat_zero] at bytesNat
    exact nonempty bytesNat.symm
  have stateEq : afterRead s ⟨0, bytes⟩ = ⟨true, 0, { s with input := append s.input bytes }⟩ := by
    rw [afterRead_ok, test]
    rfl
  rw [stateEq]
  refine ⟨fun _ => ⟨?_, by rw [sameOutput, written], outputEmpty, writtenZero⟩,
    (fun impossible => by simp [reading] at impossible),
    ⟨future.safe.outputSize, future.safe.writing⟩, ?_, future.outputSize⟩
  · show input = byteWords (append s.input bytes) ++ next.input
    rw [append_words s.input bytes (by omega), split, consumed, List.append_assoc]
  · show (append s.input bytes).data.size ≤ input.length
    rw [append_size s.input bytes (by omega)]
    exact total

/-- The bytes of a buffer are the bytes of its words. -/
theorem bytesOf_byteWords (b : Bytes) :
    ReadProgram.bytesOf b = (byteWords b).map UInt64.toUInt8 := by
  rcases b with ⟨⟨a⟩⟩
  simp [ReadProgram.bytesOf, byteWords, List.map_map, Function.comp_def]

theorem byteWords_bytesOf (b : Bytes) :
    byteWords b = (ReadProgram.bytesOf b).map UInt8.toUInt64 := by
  rcases b with ⟨⟨a⟩⟩
  rfl

/-- A read at EOF replaces the input with its report. -/
theorem future_eof {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {position next : StreamPosition}
    (future : Future input s position) (reading : s.eof = false) (bytes : Bytes)
    (empty : bytes.data.size = 0) (noInput : position.input = [])
    (consumed : position.input = byteWords bytes ++ next.input)
    (sameOutput : next.output = position.output) :
    Future input (afterRead s ⟨0, bytes⟩).state next := by
  obtain ⟨split, written, _, _⟩ := future.reading reading
  have test : (bytes.size == 0) = true := by
    simp [Bytes.size, empty]
  have nextInput : next.input = [] := by
    rw [noInput] at consumed
    exact (List.append_eq_nil_iff.mp consumed.symm).2
  have stateEq : afterRead s ⟨0, bytes⟩ =
      ⟨true, 0, ⟨Bytes.empty, TabulateProgram.tabulate s.input, 0, true⟩⟩ := by
    rw [afterRead_ok, test]
    rfl
  have small : s.input.data.size < 2 ^ 32 := Nat.lt_of_le_of_lt future.inputSize short
  have report := TabulateProgram.tabulate_eq s.input small
  have inputEq : input = byteWords s.input := by rw [split, noInput, List.append_nil]
  have nextSafe := afterRead_safe future.safe bytes
  rw [stateEq] at nextSafe ⊢
  refine ⟨(fun impossible => by cases impossible), fun _ => ⟨nextInput, rfl, ?_⟩, nextSafe,
    Nat.zero_le _, ?_⟩
  · rw [sameOutput, written, List.nil_append, remainingOutput_words nextSafe]
    show (byteWords (TabulateProgram.tabulate s.input)).drop 0 = expectedOutput input
    rw [List.drop_zero, byteWords_bytesOf, report, expectedOutput, inputBytes, inputEq,
      bytesOf_byteWords]
  · show (TabulateProgram.tabulate s.input).data.size ≤ outputLimit
    have := TabulateProgram.reportFile_length_le (ReadProgram.bytesOf s.input)
    rw [← report, ReadProgram.bytesOf_length] at this
    exact this

/-- A read of any bytes before EOF keeps the invariant. -/
theorem future_readStep {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {position next : StreamPosition}
    (future : Future input s position) (reading : s.eof = false) {bytes : Bytes}
    (consumed : position.input = byteWords bytes ++ next.input)
    (atEof : bytes.data.size = 0 → position.input = [])
    (sameOutput : next.output = position.output) :
    Future input (afterRead s ⟨0, bytes⟩).state next := by
  by_cases empty : bytes.data.size = 0
  · exact future_eof short future reading bytes empty (atEof empty) consumed sameOutput
  · exact future_read short future reading bytes empty consumed sameOutput

/-- At a stopping step the process has read its input and written the bytes of
`expectedOutput`. -/
theorem future_stop {input : List UInt64} {s : State} {position : StreamPosition}
    (future : Future input s position) (finished : ¬ s.written < s.output.size)
    (eof : s.eof = true) : position.output = expectedOutput input ∧ position.input = [] := by
  obtain ⟨noInput, _, written⟩ := future.ended eof
  rw [remainingOutput_empty future.safe finished, List.append_nil] at written
  exact ⟨written, noInput⟩

/-- Each step keeps the invariant, and a step that stops returns status 0 after the output of
`expectedOutput`, with the input read. -/
theorem future_step {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64} (short : input.length < 2 ^ 32)
    {s : State} {position : StreamPosition}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → Future input next.state nextPosition) ∧
      (next.running = false → next.status = 0 ∧
        nextPosition.output = expectedOutput input ∧ nextPosition.input = []) := by
  by_cases pending : s.written < s.output.size
  · rw [step_write pending] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput s) fun reply => .pure (afterWrite s reply))
      world trace (.returned next) final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        obtain ⟨count, nextPosition, replyEq, nextRep, sameInput, output, _⟩ :=
          streams.write_reply represented (remainingOutput_nonempty future.safe pending) operation
        cases replyEq
        simp only [writeResult, ↓reduceIte]
        have bound := (host.write_bound operation).1
        refine ⟨nextPosition, nextRep, fun _ =>
          future_afterWrite future pending _ bound sameInput output, fun stopped => ?_⟩
        rw [(afterWrite_running s _).1] at stopped
        cases stopped
  · cases eof : s.eof with
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        obtain ⟨output, noInput⟩ := future_stop future pending eof
        exact ⟨position, represented, (fun impossible => by cases impossible),
          fun _ => ⟨rfl, output, noInput⟩⟩
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
            refine ⟨nextPosition, nextRep, fun _ => future_readStep short future eof consumed atEof
              sameOutput, fun stopped => ?_⟩
            rw [(afterRead_running s _).1] at stopped
            cases stopped

end Demos.Rcv.Process
