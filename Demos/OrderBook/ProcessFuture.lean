import Demos.OrderBook.ProcessControl

/-! The invariant of [the process](Process.lean) and its preservation by each step.  `Future`
relates a reached state to the input bytes of the whole run, which are the bytes whose words the
book has received, then the carry, then the unread input.  The book satisfies the representation
invariant and represents the specification's book after the words received, and the output
written so far, followed by the output that remains, is the little-endian encoding of the
specification's events for those words.  `future_step` states that each step keeps the invariant
and that the stopping step returns the status and has written the bytes of `expectedOutput`. -/

namespace Demos.OrderBook.Process

open LeanExe LeanExe.Wasi Refinement Abstract
open Demos.StreamFold (StreamPosition StreamHost byteWords byteWords_length)

/-- The invariant of a reached state `s` at stream position `position`, for the input bytes `input`
of the whole run, of which the book has received the words of the bytes `processed`.  Before EOF
`processed` holds whole records and the carry less than one, and after EOF the input is read and
the carry holds less than one word. -/
structure Future (input : List UInt64) (s : State) (position : StreamPosition)
    (processed : List UInt64) : Prop where
  split : input = processed ++ byteWords s.carry ++ position.input
  whole : processed.length % 8 = 0
  reading : s.eof = false → processed.length % 56 = 0 ∧ s.carry.data.size < 56
  ended : s.eof = true → position.input = [] ∧ s.carry.data.size < 8
  inv : Inv (book s)
  book_eq : toSpec (book s) = (Spec.run Spec.empty (leWords processed)).1
  output : position.output ++ byteWords (remainingOutput s) =
    leBytes (Spec.encodeAll (Spec.run Spec.empty (leWords processed)).2).toList
  safe : Safe s

theorem initial_carry : initial.carry = Bytes.empty := rfl

theorem initial_eof : initial.eof = false := rfl

theorem future_initial (position : StreamPosition) (empty : position.output = []) :
    Future position.input initial position [] := by
  refine ⟨?_, rfl, fun _ => ⟨rfl, by rw [initial_carry]; decide⟩, ?_, ?_, ?_, ?_, Safe.initial⟩
  · rw [initial_carry, Demos.StreamFold.byteWords_empty]
    rfl
  · intro impossible
    rw [initial_eof] at impossible
    cases impossible
  · rw [book_initial]
    exact init_inv
  · rw [book_initial, toSpec_init]
    rfl
  · rw [empty, remainingOutput_empty Safe.initial (by decide)]
    rfl

theorem future_afterWrite {input : List UInt64} {s : State} {position next : StreamPosition}
    {processed : List UInt64} (future : Future input s position processed)
    (count : UInt64) (bound : count.toNat ≤ (remainingOutput s).data.size)
    (sameInput : next.input = position.input)
    (output : next.output = position.output ++ (byteWords (remainingOutput s)).take count.toNat) :
    Future input (afterWrite s ⟨0, count⟩).state next processed := by
  obtain ⟨oid, acct, qty, lvl, nxt, head, tail, nextId, cnt, carry, eof⟩ :=
    afterWrite_fields s ⟨0, count⟩
  have bookSame : book (afterWrite s ⟨0, count⟩).state = book s := by
    simp only [book, oid, acct, qty, lvl, nxt, head, tail, nextId, cnt]
  refine ⟨?_, future.whole, ?_, ?_, ?_, ?_, ?_, afterWrite_safe future.safe count bound⟩
  · rw [carry, sameInput]
    exact future.split
  · rw [eof, carry]
    exact future.reading
  · rw [eof, carry, sameInput]
    exact future.ended
  · rw [bookSame]
    exact future.inv
  · rw [bookSame]
    exact future.book_eq
  · rw [output, afterWrite_conservation future.safe count bound, future.output]

/-- A batch of `count` words of the carry followed by `bytes`, from a state before EOF whose output
is written, keeps the invariant with the batch's bytes added to the bytes received. -/
theorem future_runWords {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position next : StreamPosition} {processed : List UInt64}
    (future : Future input s position processed) (finished : ¬ s.written < s.output.size)
    (reading : s.eof = false) (bytes : Bytes) (count : UInt64) (eof : Bool)
    (bytesBound : bytes.data.size ≤ 4096)
    (countLe : 8 * count.toNat ≤ s.carry.data.size + bytes.data.size)
    (split : input = processed ++ (byteWords s.carry ++ byteWords bytes) ++ next.input)
    (sameOutput : next.output = position.output)
    (carryReading : eof = false → (8 * count.toNat) % 56 = 0 ∧
      s.carry.data.size + bytes.data.size - 8 * count.toNat < 56)
    (carryEnded : eof = true → next.input = [] ∧
      s.carry.data.size + bytes.data.size - 8 * count.toNat < 8) :
    Future input (runWords s bytes count eof).state next
      (processed ++ (byteWords s.carry ++ byteWords bytes).take (8 * count.toNat)) := by
  obtain ⟨wholeRecords, carrySmall⟩ := future.reading reading
  have total : s.carry.data.size + bytes.data.size < 2 ^ 64 := by omega
  have countSmall : count.toNat < 2 ^ 61 := by omega
  have startNat : (8 * count).toNat = 8 * count.toNat := by
    rw [UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  generalize hL : byteWords s.carry ++ byteWords bytes = L at split
  have lengthL : L.length = s.carry.data.size + bytes.data.size := by
    rw [← hL, List.length_append, byteWords_length, byteWords_length]
  have kept : byteWords (tailBytes s.carry bytes (8 * count)) = L.drop (8 * count.toNat) := by
    rw [tailBytes_words s.carry bytes (8 * count) total (by omega), hL, startNat]
  have keptSize : (tailBytes s.carry bytes (8 * count)).data.size =
      s.carry.data.size + bytes.data.size - 8 * count.toNat := by
    have := congrArg List.length kept
    rw [byteWords_length, List.length_drop, lengthL] at this
    exact this
  have words : (wordsOf s.carry bytes count).toList = leWords (L.take (8 * count.toNat)) := by
    rw [wordsOf_words s.carry bytes count total countLe, hL]
  have received : leWords processed ++ (wordsOf s.carry bytes count).toList =
      leWords (processed ++ L.take (8 * count.toNat)) := by
    rw [words, leWords_append future.whole]
  have takeLength : (L.take (8 * count.toNat)).length = 8 * count.toNat := by
    rw [List.length_take, lengthL]
    omega
  have nextSplit : input = (processed ++ L.take (8 * count.toNat)) ++
      L.drop (8 * count.toNat) ++ next.input := by
    rw [split]
    conv => lhs; rw [← List.take_append_drop (8 * count.toNat) L]
    simp only [List.append_assoc]
  have prefixLe : (processed ++ L.take (8 * count.toNat)).length ≤ input.length := by
    rw [nextSplit]
    simp only [List.length_append]
    omega
  have batchIds :
      (Spec.records (leWords processed ++ (wordsOf s.carry bytes count).toList)).length <
        2 ^ 64 - 1 := by
    rw [received, Spec.records_length, leWords_length]
    rw [Spec.records_length, leWords_length] at ids
    have : (processed ++ L.take (8 * count.toNat)).length / 8 ≤ input.length / 8 :=
      Nat.div_le_div_right prefixLe
    omega
  have recordsWhole : (leWords processed).length % 7 = 0 := by
    rw [leWords_length]
    omega
  obtain ⟨i1, i2, i3, i4⟩ := batch_refines future.inv future.book_eq recordsWhole
    (wordsOf s.carry bytes count) (by rw [wordsOf_size]; omega) batchIds
  obtain ⟨-, -, bookEq, carryEq, outputEq, writtenEq, eofEq⟩ := runWords_fields s bytes count eof
  have safe := runWords_safe s bytes count eof
  generalize Program.run (book s).oid (book s).acct (book s).qty (book s).lvl (book s).nxt
    (book s).head (book s).tail (book s).nextId (book s).count (wordsOf s.carry bytes count) = r
    at i1 i2 i3 i4 bookEq outputEq
  generalize (runWords s bytes count eof).state = t
    at bookEq carryEq outputEq writtenEq eofEq safe ⊢
  rw [wordsOf_size] at i4
  have eventsSmall : 8 * r.2.size < 2 ^ 64 := by
    simp only [Spec.capacity] at i4
    omega
  have written : position.output = leBytes (Spec.encodeAll
      (Spec.run Spec.empty (leWords processed)).2).toList := by
    have := future.output
    rwa [remainingOutput_empty future.safe finished, List.append_nil] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, safe⟩
  · rw [carryEq, kept]
    exact nextSplit
  · rw [List.length_append, takeLength]
    have := future.whole
    omega
  · intro notEof
    rw [eofEq] at notEof
    obtain ⟨multiple, below⟩ := carryReading notEof
    refine ⟨?_, ?_⟩
    · rw [List.length_append, takeLength]
      omega
    · rw [carryEq, keptSize]
      exact below
  · intro atEof
    rw [eofEq] at atEof
    obtain ⟨noInput, below⟩ := carryEnded atEof
    exact ⟨noInput, by rw [carryEq, keptSize]; exact below⟩
  · rw [bookEq]
    exact i1
  · rw [bookEq, i2, received]
  · rw [remainingOutput_words safe, outputEq, writtenEq, UInt64.toNat_zero, List.drop_zero,
      eventBytes_words r.2 eventsSmall, sameOutput, written, ← leBytes_append,
      ← Array.toList_append, i3, received]

/-- A read of nonempty bytes keeps the invariant. -/
theorem future_read {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position next : StreamPosition} {processed : List UInt64}
    (future : Future input s position processed) (finished : ¬ s.written < s.output.size)
    (reading : s.eof = false) (bytes : Bytes) (nonempty : bytes.data.size ≠ 0)
    (bound : bytes.data.size ≤ 4096) (consumed : position.input = byteWords bytes ++ next.input)
    (sameOutput : next.output = position.output) :
    ∃ processed', Future input (afterRead s ⟨0, bytes⟩).state next processed' := by
  obtain ⟨_, carrySmall⟩ := future.reading reading
  have bytesNat : bytes.size.toNat = bytes.data.size := Bytes.size_toNat bytes (by omega)
  have carryNat : s.carry.size.toNat = s.carry.data.size := Bytes.size_toNat s.carry (by omega)
  have test : (bytes.size == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro zero
    rw [zero, UInt64.toNat_zero] at bytesNat
    exact nonempty bytesNat.symm
  have countNat : (7 * ((s.carry.size + bytes.size) / 56)).toNat =
      7 * ((s.carry.data.size + bytes.data.size) / 56) := by
    rw [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, carryNat, bytesNat]
    simp only [UInt64.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega : s.carry.data.size + bytes.data.size < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  rw [afterRead_ok, test]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ⟨_, future_runWords ids future finished reading bytes _ false bound ?_ ?_ sameOutput
    ?_ ?_⟩
  · rw [countNat]
    omega
  · rw [future.split, consumed, List.append_assoc, List.append_assoc, List.append_assoc]
  · intro _
    rw [countNat]
    omega
  · intro impossible
    cases impossible

/-- A read at EOF keeps the invariant, with the whole words of the carry added to the bytes
received. -/
theorem future_eof {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position next : StreamPosition} {processed : List UInt64}
    (future : Future input s position processed) (finished : ¬ s.written < s.output.size)
    (reading : s.eof = false) (bytes : Bytes) (empty : bytes.data.size = 0)
    (noInput : position.input = []) (consumed : position.input = byteWords bytes ++ next.input)
    (sameOutput : next.output = position.output) :
    ∃ processed', Future input (afterRead s ⟨0, bytes⟩).state next processed' := by
  obtain ⟨_, carrySmall⟩ := future.reading reading
  have carryNat : s.carry.size.toNat = s.carry.data.size := Bytes.size_toNat s.carry (by omega)
  have test : (bytes.size == 0) = true := by
    simp [Bytes.size, empty]
  have nextInput : next.input = [] := by
    rw [noInput] at consumed
    exact (List.append_eq_nil_iff.mp consumed.symm).2
  have countNat : (s.carry.size / 8).toNat = s.carry.data.size / 8 := by
    rw [UInt64.toNat_div, carryNat]
    rfl
  have emptyData : Bytes.empty.data.size = 0 := rfl
  rw [afterRead_ok, test]
  simp only [↓reduceIte]
  refine ⟨_, future_runWords ids future finished reading Bytes.empty _ true
    (by rw [emptyData]; omega) ?_ ?_ sameOutput ?_ ?_⟩
  · rw [countNat, emptyData]
    omega
  · rw [future.split, noInput, nextInput, Demos.StreamFold.byteWords_empty]
    simp
  · intro impossible
    cases impossible
  · intro _
    refine ⟨nextInput, ?_⟩
    rw [countNat, emptyData]
    omega

/-- A read of any bytes before EOF keeps the invariant. -/
theorem future_readStep {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position next : StreamPosition} {processed : List UInt64}
    (future : Future input s position processed) (finished : ¬ s.written < s.output.size)
    (reading : s.eof = false) {bytes : Bytes} (bound : bytes.data.size ≤ (4096 : UInt64).toNat)
    (consumed : position.input = byteWords bytes ++ next.input)
    (atEof : bytes.data.size = 0 → position.input = [])
    (sameOutput : next.output = position.output) :
    ∃ processed', Future input (afterRead s ⟨0, bytes⟩).state next processed' := by
  by_cases empty : bytes.data.size = 0
  · exact future_eof ids future finished reading bytes empty (atEof empty) consumed sameOutput
  · exact future_read ids future finished reading bytes empty bound consumed sameOutput

/-- At a stopping step the process has read its input, written the bytes of `expectedOutput`, and
returns `expectedStatus`. -/
theorem future_stop {input : List UInt64} {s : State} {position : StreamPosition}
    {processed : List UInt64} (future : Future input s position processed)
    (finished : ¬ s.written < s.output.size) (eof : s.eof = true) :
    (if s.carry.size == 0 then (0 : UInt64) else 28) = expectedStatus input ∧
      position.output = expectedOutput input ∧ position.input = [] := by
  obtain ⟨noInput, carrySmall⟩ := future.ended eof
  have inputEq : input = processed ++ byteWords s.carry := by
    rw [future.split, noInput, List.append_nil]
  have words : leWords input = leWords processed := by
    rw [inputEq, leWords_append future.whole,
      leWords_short (bytes := byteWords s.carry) (by rw [byteWords_length]; exact carrySmall),
      List.append_nil]
  refine ⟨?_, ?_, noInput⟩
  · have lengthEq : input.length = processed.length + s.carry.data.size := by
      rw [inputEq, List.length_append, byteWords_length]
    have carryNat : s.carry.size.toNat = s.carry.data.size := Bytes.size_toNat s.carry (by omega)
    have whole := future.whole
    unfold expectedStatus
    by_cases zero : s.carry.data.size = 0
    · have sizeZero : s.carry.size = 0 := UInt64.toNat_inj.mp (by rw [carryNat, zero]; rfl)
      have mod : input.length % 8 = 0 := by omega
      simp [sizeZero, mod]
    · have sizeNe : s.carry.size ≠ 0 := by
        intro same
        rw [same, UInt64.toNat_zero] at carryNat
        exact zero carryNat.symm
      have sizeNonzero : (s.carry.size == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact sizeNe
      have mod : ¬ input.length % 8 = 0 := by omega
      simp [sizeNonzero, mod]
  · have := future.output
    rw [remainingOutput_empty future.safe finished, List.append_nil] at this
    rw [this, expectedOutput, words]

/-- Each step keeps the invariant, and a step that stops returns `expectedStatus` after the output
of `expectedOutput`, with the input read. -/
theorem future_step {World : Type} {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {input : List UInt64}
    (ids : (Spec.records (leWords input)).length < 2 ^ 64 - 1)
    {s : State} {position : StreamPosition} {processed : List UInt64}
    {world final : World} {trace : List Event} {next : ProcessStep State}
    (represented : rep position world) (future : Future input s position processed)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    ∃ nextPosition, rep nextPosition final ∧
      (next.running = true → ∃ processed', Future input next.state nextPosition processed') ∧
      (next.running = false → next.status = expectedStatus input ∧
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
        refine ⟨nextPosition, nextRep, fun _ => ⟨processed,
          future_afterWrite future _ bound sameInput output⟩, fun stopped => ?_⟩
        rw [(afterWrite_running s _).1] at stopped
        cases stopped
  · cases eof : s.eof with
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        obtain ⟨status, output, noInput⟩ := future_stop future pending eof
        exact ⟨position, represented, (fun impossible => by cases impossible),
          fun _ => ⟨status, output, noInput⟩⟩
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
            refine ⟨nextPosition, nextRep, fun _ => future_readStep ids future pending eof
              (host.read_bound operation).1 consumed atEof sameOutput, fun stopped => ?_⟩
            rw [(afterRead_running s _).1] at stopped
            cases stopped

end Demos.OrderBook.Process
