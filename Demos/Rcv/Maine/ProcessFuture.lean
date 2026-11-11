import Demos.Rcv.Maine.Process
import Demos.Rcv.Maine.TabulateBound
import Demos.Rcv.ProcessCorrect

/-! The invariant of [the Maine process](Process.lean) and what its `begin` does under StreamFold's
host assumptions.  `Future` is the Oakland process's invariant `Demos.Rcv.Process.Writes` for the
Maine report of the input, whose length `Demos.Rcv.Maine.TabulateProgram.reportFile_length_le`
bounds, so the Oakland process's lemmas about the steps apply.  `begin` is
`Demos.Rcv.Process.beginWith` of the Maine `tabulate` by definition, so `begin_report`, which
states that `begin` reads an input of at most `limit` bytes whole and holds its Maine report, and
`begin_long`, which states that a longer input stops the process with status `tooLong` before any
write, are the Oakland process's lemmas about `beginWith`.  `process_output` states with them that
every run of `begin` on an input of at most `limit` bytes returns a running state from which some
execution of the process writes exactly the Maine report of the input and returns status 0. -/

namespace Demos.Rcv.Maine.Process

open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition StreamHost byteWords byteWords_length)
open Demos.Rcv.Process (State initial limit tooLong process inputBytes Writes Safe
  toBytes_size_lt remainingOutput_words bytesOf_byteWords byteWords_bytesOf beginWith_report
  beginWith_long process_terminates_future)

/-- The stdout bytes for the input bytes `input`: the Maine report of the file `input`. -/
def expectedOutput (input : List UInt64) : List UInt64 :=
  (Demos.Rcv.Maine.reportFile (inputBytes input)).map UInt8.toUInt64

/-- The most bytes of a Maine report, by `TabulateProgram.reportFile_length_le`. -/
def outputLimit : Nat := 1304174

/-- The invariant of a state `s` after `begin` at stream position `position`, for the input bytes
`input` of the whole run: the input is read, and the output written so far followed by the output
that remains is the Maine report of the input. -/
abbrev Future (input : List UInt64) : State → StreamPosition → Prop :=
  Writes (expectedOutput input) outputLimit

/-- The printers' buffers have a size of `UInt64`'s, so every Maine report has fewer than 2^64
bytes. -/
theorem tabulate_size_lt (b : Bytes) :
    (TabulateProgram.tabulate b).data.size < UInt64.size := by
  unfold TabulateProgram.tabulate
  dsimp only
  split
  · exact toBytes_size_lt _
  · exact toBytes_size_lt _

/-- The state of the Maine report of the input `b`, with nothing written, satisfies the invariant
at a position that has read the input and written nothing. -/
theorem future_report (b : Bytes) (small : b.data.size < 2 ^ 32) {position : StreamPosition}
    (ended : position.input = []) (empty : position.output = []) :
    Future (byteWords b) ⟨TabulateProgram.tabulate b, 0⟩ position := by
  have report := TabulateProgram.tabulate_eq b small
  have safe := Safe.fresh (tabulate_size_lt b)
  refine ⟨ended, ?_, safe, ?_⟩
  · rw [empty, List.nil_append, remainingOutput_words safe]
    show (byteWords (TabulateProgram.tabulate b)).drop 0 = expectedOutput (byteWords b)
    rw [List.drop_zero, expectedOutput, inputBytes, ← bytesOf_byteWords, ← report]
    exact byteWords_bytesOf _
  · show (TabulateProgram.tabulate b).data.size ≤ outputLimit
    have := TabulateProgram.reportFile_length_le (ReadProgram.bytesOf b)
    rw [← report, ReadProgram.bytesOf_length] at this
    exact this

/-- Every run of `begin` on an input of at most `limit` bytes, from a position with no output,
returns the running state of the Maine report of the input with status 0, at a position that has
read the input and written nothing. -/
theorem begin_report {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {position : StreamPosition}
    (size : position.input.length ≤ limit.toNat) (empty : position.output = [])
    {world trace outcome final} (represented : rep position world)
    (execution : LeanExe.Wasi.Exec host begin world trace outcome final) :
    ∃ next nextPosition, outcome = .returned next ∧ rep nextPosition final ∧
      next.running = true ∧ next.status = 0 ∧
      Future position.input next.state nextPosition :=
  beginWith_report (tab := TabulateProgram.tabulate) (expected := expectedOutput) future_report
    streams size empty represented execution

/-- Every run of `begin` on an input of more than `limit` bytes stops with status `tooLong`, at a
position whose output is the output before it. -/
theorem begin_long {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {position : StreamPosition}
    (size : limit.toNat < position.input.length)
    {world trace outcome final} (represented : rep position world)
    (execution : LeanExe.Wasi.Exec host begin world trace outcome final) :
    ∃ nextPosition, outcome = .returned ⟨false, tooLong, initial⟩ ∧
      rep nextPosition final ∧
      nextPosition.output = position.output :=
  beginWith_long (tab := TabulateProgram.tabulate) streams size represented execution

/-- Every run of `begin` on an input of at most `limit` bytes from an empty output history
returns a running state with status 0, from which some execution of the process writes exactly
the bytes of the Maine report of the input and returns status 0. -/
theorem process_output {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world : World} (represented : rep position world)
    (empty : position.output = []) (size : position.input.length ≤ limit.toNat)
    {trace : List Event} {outcome : Outcome (ProcessStep State)} {after : World}
    (started : LeanExe.Wasi.Exec host begin world trace outcome after) :
    ∃ first, outcome = .returned first ∧ first.running = true ∧ first.status = 0 ∧
      ∃ rest final next,
        LeanExe.Wasi.Process.Exec host process first.state after rest (.returned 0) final ∧
        rep next final ∧ next.output = expectedOutput position.input ∧ next.input = [] := by
  obtain ⟨first, firstPosition, same, firstRep, running, status, future⟩ :=
    begin_report streams size empty represented started
  exact ⟨first, same, running, status, process_terminates_future streams firstRep future⟩

end Demos.Rcv.Maine.Process
