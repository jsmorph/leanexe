import Demos.OrderBook.ProcessCodec
import Demos.OrderBook.ProcessBatch
import Demos.StreamFold.StreamHost
import Verified.Wasi.ProcessTotalSource

/-! The control of [the process](Process.lean): the bounds on the output that each step keeps, the
accounting of partial writes, the fields of a batch, and the termination of the process under
StreamFold's `StreamProgress`.  The rank orders the unread input, the EOF flag, the unwritten
output, and the host's credit for zero-byte writes lexicographically, and each running step lowers
it. -/

namespace Demos.OrderBook.Process

open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamProgress byteWords byteWords_length byteWords_get byteWords_build_get
  bytes_get_narrow)

/-- The output has fewer than 2^64 bytes, and either it is empty with nothing written or some of it
remains to be written. -/
structure Safe (s : State) : Prop where
  outputSize : s.output.data.size < UInt64.size
  writing : (s.output.data.size = 0 ∧ s.written = 0) ∨ s.written < s.output.size

theorem Safe.initial : Safe initial :=
  ⟨by change 0 < UInt64.size; decide, Or.inl ⟨rfl, rfl⟩⟩

theorem Safe.output_toNat {s : State} (safe : Safe s) : s.output.size.toNat = s.output.data.size :=
  Bytes.size_toNat s.output safe.outputSize

theorem Safe.written_le {s : State} (safe : Safe s) : s.written.toNat ≤ s.output.data.size := by
  rcases safe.writing with ⟨empty, zero⟩ | pending
  · simp only [empty, zero, UInt64.toNat_zero, Nat.le_refl]
  · have less := UInt64.lt_iff_toNat_lt.mp pending
    rw [safe.output_toNat] at less
    omega

theorem Safe.no_output {s : State} (safe : Safe s) (finished : ¬ s.written < s.output.size) :
    s.output.data.size = 0 ∧ s.written = 0 := by
  rcases safe.writing with empty | pending
  · exact empty
  · exact False.elim (finished pending)

/-! ## Partial writes -/

theorem remainingOutput_size {s : State} (safe : Safe s) :
    (remainingOutput s).data.size = s.output.data.size - s.written.toNat := by
  unfold remainingOutput
  rw [Bytes.data_size_build, UInt64.toNat_sub_of_le]
  · rw [safe.output_toNat]
  · exact UInt64.le_iff_toNat_le.mpr (by rw [safe.output_toNat]; exact safe.written_le)

theorem remainingOutput_words {s : State} (safe : Safe s) :
    byteWords (remainingOutput s) = (byteWords s.output).drop s.written.toNat := by
  have written := safe.written_le
  have le : s.written ≤ s.output.size :=
    UInt64.le_iff_toNat_le.mpr (by rw [safe.output_toNat]; exact written)
  have countNat : (s.output.size - s.written).toNat = s.output.data.size - s.written.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ le, safe.output_toNat]
  unfold remainingOutput
  apply List.ext_getElem
  · simp only [byteWords_length, Bytes.data_size_build, List.length_drop, countNat]
  · intro index left right
    have indexBound : index < s.output.data.size - s.written.toNat := by
      simpa only [byteWords_length, Bytes.data_size_build, countNat] using left
    have indexNat : (UInt64.ofNat index).toNat = index := UInt64.toNat_ofNat_of_lt' (by
      have := safe.outputSize
      omega)
    have sumNat : (s.written + UInt64.ofNat index).toNat = s.written.toNat + index := by
      rw [UInt64.toNat_add, indexNat]
      exact Nat.mod_eq_of_lt (show s.written.toNat + index < UInt64.size by
        have := safe.outputSize
        omega)
    rw [byteWords_build_get (s.output.size - s.written)
      (fun i => s.output.get (s.written + i)) index (by rw [countNat]; exact indexBound),
      bytes_get_narrow]
    rw [List.getElem_drop]
    simpa only [sumNat] using
      (byteWords_get s.output (s.written + UInt64.ofNat index) (by omega)).symm

theorem remainingOutput_nonempty {s : State} (safe : Safe s) (pending : s.written < s.output.size) :
    0 < (remainingOutput s).data.size := by
  rw [remainingOutput_size safe]
  have less := UInt64.lt_iff_toNat_lt.mp pending
  rw [safe.output_toNat] at less
  omega

theorem remainingOutput_empty {s : State} (safe : Safe s) (finished : ¬ s.written < s.output.size) :
    byteWords (remainingOutput s) = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [byteWords_length, remainingOutput_size safe, (safe.no_output finished).1]
  simp

theorem afterWrite_sum {s : State} (safe : Safe s) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput s).data.size) :
    (s.written + count).toNat = s.written.toNat + count.toNat ∧
      s.written.toNat + count.toNat ≤ s.output.data.size := by
  rw [remainingOutput_size safe] at bound
  have old := safe.written_le
  have total : s.written.toNat + count.toNat ≤ s.output.data.size := by omega
  exact ⟨by rw [UInt64.toNat_add, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt total safe.outputSize)],
    total⟩

theorem afterWrite_safe {s : State} (safe : Safe s) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput s).data.size) :
    Safe (afterWrite s ⟨0, count⟩).state := by
  obtain ⟨sumNat, sumBound⟩ := afterWrite_sum safe count bound
  simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨by change 0 < UInt64.size; decide, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i different
    simp only [beq_iff_eq] at different
    refine ⟨safe.outputSize, Or.inr ?_⟩
    apply UInt64.lt_iff_toNat_lt.mpr
    have differentNat : (s.written + count).toNat ≠ s.output.size.toNat := by
      intro equal
      exact different (UInt64.toNat_inj.mp equal)
    rw [sumNat, safe.output_toNat] at differentNat ⊢
    omega

theorem afterWrite_running (s : State) (count : UInt64) :
    (afterWrite s ⟨0, count⟩).running = true ∧ (afterWrite s ⟨0, count⟩).status = 0 := by
  simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split <;> exact ⟨rfl, rfl⟩

theorem afterWrite_fields (s : State) (reply : WriteResult) :
    (afterWrite s reply).state.oid = s.oid ∧ (afterWrite s reply).state.acct = s.acct ∧
      (afterWrite s reply).state.qty = s.qty ∧ (afterWrite s reply).state.lvl = s.lvl ∧
      (afterWrite s reply).state.nxt = s.nxt ∧ (afterWrite s reply).state.head = s.head ∧
      (afterWrite s reply).state.tail = s.tail ∧ (afterWrite s reply).state.nextId = s.nextId ∧
      (afterWrite s reply).state.count = s.count ∧ (afterWrite s reply).state.carry = s.carry ∧
      (afterWrite s reply).state.eof = s.eof := by
  unfold afterWrite
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem afterWrite_remaining {s : State} (safe : Safe s) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput s).data.size) :
    byteWords (remainingOutput (afterWrite s ⟨0, count⟩).state) =
      (byteWords (remainingOutput s)).drop count.toNat := by
  have sum := afterWrite_sum safe count bound
  have nextSafe := afterWrite_safe safe count bound
  rw [remainingOutput_words nextSafe, remainingOutput_words safe]
  simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i complete
    have same : s.written + count = s.output.size := by simpa using complete
    have sameNat := congrArg UInt64.toNat same
    rw [sum.1, safe.output_toNat] at sameNat
    simp only [Demos.StreamFold.byteWords_empty, UInt64.toNat_zero, List.drop_zero, List.drop_drop]
    exact (List.drop_eq_nil_of_le (by rw [byteWords_length]; omega)).symm
  · simp only [sum.1, List.drop_drop]

theorem afterWrite_conservation {s : State} (safe : Safe s) (count : UInt64)
    (bound : count.toNat ≤ (remainingOutput s).data.size) (committed : List UInt64) :
    (committed ++ (byteWords (remainingOutput s)).take count.toNat) ++
        byteWords (remainingOutput (afterWrite s ⟨0, count⟩).state) =
      committed ++ byteWords (remainingOutput s) := by
  rw [afterWrite_remaining safe count bound, List.append_assoc, List.take_append_drop]

/-! ## Batches -/

/-- The fields of the state after a batch. -/
theorem runWords_fields (s : State) (input : Bytes) (count : UInt64) (eof : Bool) :
    (runWords s input count eof).running = true ∧ (runWords s input count eof).status = 0 ∧
      book (runWords s input count eof).state =
        (Program.run (book s).oid (book s).acct (book s).qty (book s).lvl (book s).nxt
          (book s).head (book s).tail (book s).nextId (book s).count
          (wordsOf s.carry input count)).1 ∧
      (runWords s input count eof).state.carry = tailBytes s.carry input (8 * count) ∧
      (runWords s input count eof).state.output =
        eventBytes (Program.run (book s).oid (book s).acct (book s).qty (book s).lvl (book s).nxt
          (book s).head (book s).tail (book s).nextId (book s).count
          (wordsOf s.carry input count)).2 ∧
      (runWords s input count eof).state.written = 0 ∧
      (runWords s input count eof).state.eof = eof :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem runWords_safe (s : State) (input : Bytes) (count : UInt64) (eof : Bool) :
    Safe (runWords s input count eof).state := by
  obtain ⟨-, -, -, -, output, written, -⟩ := runWords_fields s input count eof
  generalize (runWords s input count eof).state = t at output written
  have size : t.output.data.size < UInt64.size := by
    rw [output, eventBytes_size]
    exact UInt64.toNat_lt _
  refine ⟨size, ?_⟩
  by_cases empty : t.output.data.size = 0
  · exact Or.inl ⟨empty, written⟩
  · refine Or.inr ?_
    rw [written, UInt64.lt_iff_toNat_lt, Bytes.size_toNat _ size, UInt64.toNat_zero]
    omega

theorem afterRead_ok (s : State) (bytes : Bytes) :
    afterRead s ⟨0, bytes⟩ =
      if bytes.size == 0 then runWords s Bytes.empty (s.carry.size / 8) true
      else runWords s bytes (7 * ((s.carry.size + bytes.size) / 56)) false := by
  simp [afterRead]

theorem afterRead_safe (s : State) (bytes : Bytes) : Safe (afterRead s ⟨0, bytes⟩).state := by
  rw [afterRead_ok]
  split <;> exact runWords_safe _ _ _ _

theorem afterRead_running (s : State) (bytes : Bytes) :
    (afterRead s ⟨0, bytes⟩).running = true ∧ (afterRead s ⟨0, bytes⟩).status = 0 := by
  rw [afterRead_ok]
  split <;> exact ⟨(runWords_fields _ _ _ _).1, (runWords_fields _ _ _ _).2.1⟩

theorem afterRead_eof (s : State) (bytes : Bytes) :
    (afterRead s ⟨0, bytes⟩).state.eof = (bytes.size == 0) := by
  rw [afterRead_ok]
  split
  · rename_i empty
    rw [empty]
    exact (runWords_fields _ _ _ _).2.2.2.2.2.2
  · rename_i nonempty
    simp only [Bool.not_eq_true] at nonempty
    rw [nonempty]
    exact (runWords_fields _ _ _ _).2.2.2.2.2.2

/-! ## Rank -/

abbrev Rank := Nat × Nat × Nat × Nat

abbrev rankOrder : WellFoundedRelation Rank :=
  Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel))

abbrev RankLt := rankOrder.rel

theorem rank_wellFounded : WellFounded RankLt := rankOrder.wf

/-- The unread input, the EOF flag, the unwritten output, and the zero-write credit. -/
def rank (unread zeroWrites : Ghost → Nat) (s : State) (ghost : Ghost) : Rank :=
  (unread ghost, if s.eof then 0 else 1, s.output.data.size - s.written.toNat, zeroWrites ghost)

theorem rank_afterRead (unread zeroWrites : Ghost → Nat) {before after : Ghost}
    {s : State} {bytes : Bytes} (eof : s.eof = false) (unreadLe : unread after ≤ unread before)
    (nonempty : bytes.data.size ≠ 0 → unread after < unread before) :
    RankLt (rank unread zeroWrites (afterRead s ⟨0, bytes⟩).state after)
      (rank unread zeroWrites s before) := by
  by_cases decreased : unread after < unread before
  · exact Prod.Lex.left _ _ decreased
  · have same : unread after = unread before := by omega
    have empty : bytes.data.size = 0 := by
      by_cases empty : bytes.data.size = 0
      · exact empty
      · exact False.elim (decreased (nonempty empty))
    have bytesSize : bytes.size = 0 := by simp [Bytes.size, empty]
    have nextEof : (afterRead s ⟨0, bytes⟩).state.eof = true := by
      simp [afterRead_eof, bytesSize]
    unfold rank
    rw [same, nextEof, eof]
    apply Prod.Lex.right
    exact Prod.Lex.left _ _ (show (0 : Nat) < 1 by decide)

theorem rank_afterWrite (unread zeroWrites : Ghost → Nat) {before after : Ghost}
    {s : State} (safe : Safe s) (pending : s.written < s.output.size)
    (count : UInt64) (bound : count.toNat ≤ (remainingOutput s).data.size)
    (same : unread after = unread before)
    (zero : count = 0 → zeroWrites after < zeroWrites before) :
    RankLt (rank unread zeroWrites (afterWrite s ⟨0, count⟩).state after)
      (rank unread zeroWrites s before) := by
  have pendingNat := UInt64.lt_iff_toNat_lt.mp pending
  rw [safe.output_toNat] at pendingNat
  obtain ⟨sumNat, sumBound⟩ := afterWrite_sum safe count bound
  by_cases countZero : count = 0
  · have different : s.written ≠ s.output.size := by
      intro equal
      rw [equal] at pending
      exact (UInt64.lt_irrefl _) pending
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      countZero, UInt64.add_zero, beq_iff_eq, different]
    unfold rank
    rw [same]
    apply Prod.Lex.right
    apply Prod.Lex.right
    apply Prod.Lex.right
    exact zero countZero
  · have countPositive : 0 < count.toNat := by
      have nonzero : count.toNat ≠ 0 := by
        intro sameNat
        apply countZero
        exact UInt64.toNat_inj.mp (by simpa using sameNat)
      omega
    simp only [afterWrite, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split
    · unfold rank
      rw [same]
      apply Prod.Lex.right
      apply Prod.Lex.right
      exact Prod.Lex.left _ _ (Nat.sub_pos_of_lt pendingNat)
    · unfold rank
      rw [same]
      apply Prod.Lex.right
      apply Prod.Lex.right
      have smaller : s.output.data.size - (s.written + count).toNat <
          s.output.data.size - s.written.toNat := by rw [sumNat]; omega
      exact Prod.Lex.left _ _ smaller

/-! ## Termination -/

def Advances (rep : Ghost → World → Prop) (unread zeroWrites : Ghost → Nat)
    (s : State) (ghost : Ghost) (next : ProcessStep State) (final : World) : Prop :=
  ∃ nextGhost, rep nextGhost final ∧ Safe next.state ∧
    (next.running = false → next.status = 0 ∨ next.status = 28) ∧
    (next.running = true →
      RankLt (rank unread zeroWrites next.state nextGhost) (rank unread zeroWrites s ghost))

theorem writeStep_advances {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State} (ready : rep ghost world) (safe : Safe s)
    (pending : s.written < s.output.size)
    (execution : LeanExe.Wasi.Exec host (writeStep s) world trace (.returned next) final) :
    Advances rep unread zeroWrites s ghost next final := by
  change LeanExe.Wasi.Exec host
    (.write .stdout (remainingOutput s) fun reply => .pure (afterWrite s reply))
    world trace (.returned next) final at execution
  cases execution with
  | write_return operation continuation =>
      cases continuation
      obtain ⟨count, nextGhost, replyEq, nextRep, sameInput, zeroDrop⟩ :=
        progress.write_reply ready (remainingOutput_nonempty safe pending) operation
      cases replyEq
      simp only [writeResult, ↓reduceIte]
      have countBound := (host.write_bound operation).1
      refine ⟨nextGhost, nextRep, afterWrite_safe safe _ countBound, ?_, ?_⟩
      · intro stopped
        rw [(afterWrite_running s _).1] at stopped
        cases stopped
      · intro _
        exact rank_afterWrite unread zeroWrites safe pending _ countBound sameInput zeroDrop

theorem readStep_advances {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State} (ready : rep ghost world) (eof : s.eof = false)
    (execution : LeanExe.Wasi.Exec host (readStep s) world trace (.returned next) final) :
    Advances rep unread zeroWrites s ghost next final := by
  change LeanExe.Wasi.Exec host
    (.read 4096 fun reply => .pure (afterRead s reply))
    world trace (.returned next) final at execution
  cases execution with
  | read_reject capacity continuation =>
      exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
  | read_return capacity operation continuation =>
      cases continuation
      obtain ⟨bytes, nextGhost, replyEq, nextRep, inputLe, nonemptyDrop⟩ :=
        progress.read_reply ready operation
      cases replyEq
      simp only [readResult, ↓reduceIte]
      refine ⟨nextGhost, nextRep, afterRead_safe s _, ?_, ?_⟩
      · intro stopped
        rw [(afterRead_running s _).1] at stopped
        cases stopped
      · intro _
        exact rank_afterRead unread zeroWrites eof inputLe nonemptyDrop

theorem step_write {s : State} (pending : s.written < s.output.size) :
    step s = writeStep s := by
  simp [step, pending]

theorem step_stop {s : State} (finished : ¬ s.written < s.output.size) (eof : s.eof = true) :
    step s = .pure ⟨false, if s.carry.size == 0 then 0 else 28, s⟩ := by
  simp [step, finished, eof] <;> rfl

theorem step_read {s : State} (finished : ¬ s.written < s.output.size) (eof : s.eof = false) :
    step s = readStep s := by
  simp [step, finished, eof]

theorem stop_status (s : State) :
    (if s.carry.size == 0 then (0 : UInt64) else 28) = 0 ∨
      (if s.carry.size == 0 then (0 : UInt64) else 28) = 28 := by
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem step_advances {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {next : ProcessStep State} (ready : rep ghost world) (safe : Safe s)
    (execution : LeanExe.Wasi.Exec host (step s) world trace (.returned next) final) :
    Advances rep unread zeroWrites s ghost next final := by
  by_cases pending : s.written < s.output.size
  · rw [step_write pending] at execution
    exact writeStep_advances progress ready safe pending execution
  · cases eof : s.eof with
    | false =>
        rw [step_read pending eof] at execution
        exact readStep_advances progress ready eof execution
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        exact ⟨ghost, ready, safe, fun _ => stop_status s,
          fun impossible => False.elim (Bool.noConfusion impossible)⟩

theorem step_exists {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world : World} (ready : rep ghost world) (safe : Safe s) :
    ∃ next trace final, LeanExe.Wasi.Exec host (step s) world trace (.returned next) final := by
  by_cases pending : s.written < s.output.size
  · obtain ⟨count, final, operation⟩ :=
      progress.write_available ghost world (remainingOutput s) ready
        (remainingOutput_nonempty safe pending)
    refine ⟨afterWrite s ⟨0, count⟩,
      [.write .stdout (remainingOutput s) (.returned 0 count)], final, ?_⟩
    rw [step_write pending]
    exact .write_return operation (.pure final _)
  · cases eof : s.eof with
    | false =>
        obtain ⟨bytes, final, operation⟩ := progress.read_available ghost world ready
        refine ⟨afterRead s ⟨0, bytes⟩, [.read 4096 (.returned 0 bytes)], final, ?_⟩
        rw [step_read pending eof]
        exact .read_return (by decide) operation (.pure final _)
    | true =>
        refine ⟨⟨false, if s.carry.size == 0 then 0 else 28, s⟩, [], world, ?_⟩
        rw [step_stop pending eof]
        exact .pure world _

theorem step_returned {host : Host World} {rep : Ghost → World → Prop}
    {unread zeroWrites : Ghost → Nat} (progress : StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world final : World} {trace : List Event}
    {outcome : Outcome (ProcessStep State)} (ready : rep ghost world) (safe : Safe s)
    (execution : LeanExe.Wasi.Exec host (step s) world trace outcome final) :
    ∃ next, outcome = .returned next := by
  by_cases pending : s.written < s.output.size
  · rw [step_write pending] at execution
    change LeanExe.Wasi.Exec host
      (.write .stdout (remainingOutput s) fun reply => .pure (afterWrite s reply))
      world trace outcome final at execution
    cases execution with
    | write_return operation continuation =>
        cases continuation
        exact ⟨_, rfl⟩
    | write_trap operation =>
        obtain ⟨_, _, impossible, _⟩ :=
          progress.write_reply ready (remainingOutput_nonempty safe pending) operation
        cases impossible
  · cases eof : s.eof with
    | false =>
        rw [step_read pending eof] at execution
        change LeanExe.Wasi.Exec host (.read 4096 fun reply => .pure (afterRead s reply))
          world trace outcome final at execution
        cases execution with
        | read_reject capacity continuation =>
            exact False.elim ((by decide : ¬ 2 ^ 32 ≤ (4096 : UInt64).toNat) capacity)
        | read_return capacity operation continuation =>
            cases continuation
            exact ⟨_, rfl⟩
        | read_trap capacity operation =>
            obtain ⟨_, _, impossible, _⟩ := progress.read_reply ready operation
            cases impossible
    | true =>
        rw [step_stop pending eof] at execution
        cases execution
        exact ⟨_, rfl⟩

/-- From every state whose output bounds hold, some execution of the process returns status 0 or
28. -/
theorem process_terminates {World Ghost : Type} {host : Host World}
    {rep : Ghost → World → Prop} {unread zeroWrites : Ghost → Nat}
    (progress : StreamProgress host rep unread zeroWrites)
    {s : State} {ghost : Ghost} {world : World} (ready : rep ghost world) (safe : Safe s) :
    ∃ trace status final finalGhost,
      Process.Exec host process s world trace (.returned status) final ∧
      (status = 0 ∨ status = 28) ∧ rep finalGhost final := by
  let represented (config : State × Ghost) (s : State) (world : World) : Prop :=
    config.1 = s ∧ rep config.2 world ∧ Safe s
  let measure (config : State × Ghost) := rank unread zeroWrites config.1 config.2
  obtain ⟨trace, status, final, config, finalState, execution, statusOk, finalRep⟩ :=
    Process.exec_of_wellFounded (host := host) (process := process) represented
      (InvImage RankLt measure) (InvImage.wf measure rank_wellFounded)
      (fun status => status = 0 ∨ status = 28)
      (fun config current world held => by
        obtain ⟨s, ghost⟩ := config
        obtain ⟨rfl, ready, safe⟩ := held
        obtain ⟨next, trace, final, execution⟩ := step_exists progress ready safe
        obtain ⟨nextGhost, nextRep, nextSafe, statusOk, smaller⟩ :=
          step_advances progress ready safe execution
        exact ⟨next, trace, final, (next.state, nextGhost), execution,
          ⟨rfl, nextRep, nextSafe⟩, statusOk, smaller⟩)
      (ghost := (s, ghost)) (state := s) (world := world) ⟨rfl, ready, safe⟩
  exact ⟨trace, status, final, config.2, execution, statusOk, finalRep.2.1⟩

end Demos.OrderBook.Process
