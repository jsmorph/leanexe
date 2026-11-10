import Demos.Rcv.ProcessControl
import Demos.Rcv.TabulateBound
import Demos.StreamFold.ReadAll
import LeanExe.Wasi.Bind

/-! The invariant of [the process](Process.lean) and what `begin` and each step do under
StreamFold's host assumptions.  `begin_report` states that `begin` reads an input of at most
`limit` bytes whole and holds its report, and `begin_long` that a longer input stops the process
with status `tooLong` before any write.  `Future` relates a state after `begin` to the input: the
input is read, and the output written so far followed by the output that remains is the report of
the input.  `future_step` states that each step keeps the invariant and that the stopping step
returns status 0 after writing the report. -/

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

theorem limit_toNat : limit.toNat = 50000000 := rfl

/-- The invariant of a state `s` after `begin` at stream position `position`, for the input
bytes `input` of the whole run. -/
structure Future (input : List UInt64) (s : State) (position : StreamPosition) : Prop where
  ended : position.input = []
  written : position.output ++ byteWords (remainingOutput s) = expectedOutput input
  safe : Safe s
  outputSize : s.output.data.size ≤ outputLimit

/-- The bytes of a buffer are the bytes of its words. -/
theorem bytesOf_byteWords (b : Bytes) :
    ReadProgram.bytesOf b = (byteWords b).map UInt64.toUInt8 := by
  rcases b with ⟨⟨a⟩⟩
  simp [ReadProgram.bytesOf, byteWords, List.map_map, Function.comp_def]

theorem byteWords_bytesOf (b : Bytes) :
    byteWords b = (ReadProgram.bytesOf b).map UInt8.toUInt64 := by
  rcases b with ⟨⟨a⟩⟩
  rfl

/-- The state of the report of the input `b`, with nothing written, satisfies the invariant at a
position that has read the input and written nothing. -/
theorem future_report (b : Bytes) (small : b.data.size < 2 ^ 32) {position : StreamPosition}
    (ended : position.input = []) (empty : position.output = []) :
    Future (byteWords b) ⟨TabulateProgram.tabulate b, 0⟩ position := by
  have report := TabulateProgram.tabulate_eq b small
  have safe := report_safe b
  refine ⟨ended, ?_, safe, ?_⟩
  · rw [empty, List.nil_append, remainingOutput_words safe]
    show (byteWords (TabulateProgram.tabulate b)).drop 0 = expectedOutput (byteWords b)
    rw [List.drop_zero, expectedOutput, inputBytes, ← bytesOf_byteWords, ← report]
    exact byteWords_bytesOf _
  · show (TabulateProgram.tabulate b).data.size ≤ outputLimit
    have := TabulateProgram.reportFile_length_le (ReadProgram.bytesOf b)
    rw [← report, ReadProgram.bytesOf_length] at this
    exact this

theorem begin_exec {World : Type} {host : Host World} {world trace outcome final}
    (execution : LeanExe.Wasi.Exec host begin world trace outcome final) :
    ∃ after first middle rest,
      LeanExe.Wasi.Exec host (readAll limit) world first middle after ∧
      Continue host (fun input => Action.pure (started input)) after middle rest outcome final ∧
      trace = first ++ rest := by
  change LeanExe.Wasi.Exec host (Action.bind (readAll limit) fun input =>
    Action.pure (started input)) world trace outcome final at execution
  exact Exec.bind_iff.mp execution

/-- Every run of `begin` on an input of at most `limit` bytes, from a position with no output,
returns the running state of the report of the input with status 0, at a position that has read
the input and written nothing. -/
theorem begin_report {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {position : StreamPosition}
    (size : position.input.length ≤ limit.toNat) (empty : position.output = [])
    {world trace outcome final} (represented : rep position world)
    (execution : LeanExe.Wasi.Exec host begin world trace outcome final) :
    ∃ next nextPosition, outcome = .returned next ∧ rep nextPosition final ∧
      next.running = true ∧ next.status = 0 ∧
      Future position.input next.state nextPosition := by
  obtain ⟨after, first, middle, rest, reading, continued, _⟩ := begin_exec execution
  obtain ⟨result, nextPosition, same, nextRep, errno, whole, ended, output⟩ :=
    streams.readAll_whole (by decide) size represented reading
  subst same
  change LeanExe.Wasi.Exec host (.pure (started result)) after rest outcome final at continued
  cases continued
  have resultSize : result.bytes.data.size ≤ limit.toNat := by
    rw [← whole, byteWords_length] at size
    exact size
  have small : result.bytes.data.size < 2 ^ 32 := by rw [limit_toNat] at resultSize; omega
  have within : ¬limit < result.bytes.size := by
    rw [UInt64.lt_iff_toNat_lt, Bytes.size_toNat _ (by omega)]
    omega
  have startedEq :
      started result = ⟨true, 0, ⟨TabulateProgram.tabulate result.bytes, 0⟩⟩ := by
    simp [started, errno, within]
  refine ⟨_, nextPosition, rfl, nextRep, by rw [startedEq], by rw [startedEq], ?_⟩
  rw [startedEq, ← whole]
  exact future_report result.bytes small ended (output.trans empty)

/-- Every run of `begin` on an input of more than `limit` bytes stops with status `tooLong`, at a
position whose output is the output before it. -/
theorem begin_long {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {position : StreamPosition}
    (size : limit.toNat < position.input.length)
    {world trace outcome final} (represented : rep position world)
    (execution : LeanExe.Wasi.Exec host begin world trace outcome final) :
    ∃ nextPosition, outcome = .returned ⟨false, tooLong, initial⟩ ∧
      rep nextPosition final ∧
      nextPosition.output = position.output := by
  obtain ⟨after, first, middle, rest, reading, continued, _⟩ := begin_exec execution
  obtain ⟨result, nextPosition, same, nextRep, errno, above, output⟩ :=
    streams.readAll_long (by decide) size represented reading
  subst same
  change LeanExe.Wasi.Exec host (.pure (started result)) after rest outcome final at continued
  cases continued
  have bound := readAll_size reading
  have overLimit : limit < result.bytes.size := by
    rw [UInt64.lt_iff_toNat_lt, Bytes.size_toNat _ (by rw [limit_toNat] at bound; omega)]
    exact above
  refine ⟨nextPosition, ?_, nextRep, output⟩
  simp [started, errno, overLimit]

/-- A write keeps the invariant. -/
theorem future_afterWrite {input : List UInt64} {s : State} {position next : StreamPosition}
    (future : Future input s position)
    (count : UInt64) (bound : count.toNat ≤ (remainingOutput s).data.size)
    (sameInput : next.input = position.input)
    (output : next.output = position.output ++ (byteWords (remainingOutput s)).take count.toNat) :
    Future input (afterWrite s ⟨0, count⟩).state next := by
  refine ⟨by rw [sameInput, future.ended], ?_, afterWrite_safe future.safe count bound,
    Nat.le_trans (afterWrite_output_le s _) future.outputSize⟩
  rw [output, afterWrite_conservation future.safe count bound, future.written]

/-- At a stopping step the process has written the bytes of `expectedOutput`. -/
theorem future_stop {input : List UInt64} {s : State} {position : StreamPosition}
    (future : Future input s position) (finished : ¬ s.written < s.output.size) :
    position.output = expectedOutput input ∧ position.input = [] := by
  have written := future.written
  rw [remainingOutput_empty future.safe finished, List.append_nil] at written
  exact ⟨written, future.ended⟩

/-- Each step keeps the invariant, and a step that stops returns status 0 after the output of
`expectedOutput`, with the input read. -/
theorem future_step {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
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
          future_afterWrite future _ bound sameInput output, fun stopped => ?_⟩
        rw [(afterWrite_running s _).1] at stopped
        cases stopped
  · rw [step_stop pending] at execution
    cases execution
    obtain ⟨output, noInput⟩ := future_stop future pending
    exact ⟨position, represented, (fun impossible => by cases impossible),
      fun _ => ⟨rfl, output, noInput⟩⟩

end Demos.Rcv.Process
