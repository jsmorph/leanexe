import Demos.StreamFold.StreamHost
import LeanExe.Wasi.ReadAll

/-! `readAll` under StreamFold's host assumptions.  Every run of `readAll limit` returns errno 0
with a prefix of the unread input, leaves the output unchanged, and either reads to EOF or returns
more than `limit` bytes.  An input of at most `limit` bytes is therefore returned whole, and a
longer one returns more than `limit` bytes. -/

namespace Demos.StreamFold

open LeanExe LeanExe.Wasi

theorem byteWords_appendBytes (first second : Bytes) :
    byteWords (appendBytes first second) = byteWords first ++ byteWords second := by
  simp only [byteWords, appendBytes, ByteArray.data_append, Array.toList_append, List.map_append]

/-- A run of the loop from a state that has ended returns the state's errno and bytes at once. -/
theorem readAll_done {World : Type} {host : Host World} {limit : UInt64}
    {state : ReadAllState} (done : state.done = true) :
    ∀ {remaining index world trace outcome final},
      LoopExec host remaining index state readAllTest (readAllRead limit) readAllResult world
        trace outcome final →
      outcome = .returned ⟨state.errno, state.held⟩ ∧ final = world ∧ trace = []
  | 0, _, _, _, _, _, execution => by
    cases execution with
    | zero next => cases next; exact ⟨rfl, rfl, rfl⟩
  | _ + 1, _, _, _, _, _, execution => by
    cases execution with
    | stop _ next => cases next; exact ⟨rfl, rfl, rfl⟩
    | next test _ _ => simp [readAllTest, done] at test
    | exit test _ => simp [readAllTest, done] at test
    | trap test _ => simp [readAllTest, done] at test

/-- What a run of `readAll` returns under the host assumptions, from the input `total`. -/
def ReadAllReturns {World : Type} (rep : StreamPosition → World → Prop) (limit : UInt64)
    (total : List UInt64) (position : StreamPosition) (outcome : Outcome ReadResult)
    (final : World) : Prop :=
  ∃ result next, outcome = .returned result ∧ rep next final ∧ result.errno = 0 ∧
    total = byteWords result.bytes ++ next.input ∧ next.output = position.output ∧
    (next.input = [] ∨ limit.toNat < result.bytes.data.size)

private theorem readAllLoop_stream {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep) {limit : UInt64}
    (total : List UInt64) :
    ∀ (remaining index : Nat) (held : Bytes) (position : StreamPosition)
      {world trace outcome final},
      rep position world → total = byteWords held ++ position.input →
      held.data.size ≤ limit.toNat → limit.toNat + 2 ≤ remaining + held.data.size →
      LoopExec host remaining index (⟨0, held, false⟩ : ReadAllState) readAllTest
        (readAllRead limit) readAllResult world trace outcome final →
      ReadAllReturns rep limit total position outcome final
  | 0, _, _, _, _, _, _, _, _, _, small, enough, _ => by omega
  | remaining + 1, index, held, position, world, trace, outcome, final, represented, split,
      small, enough, execution => by
    cases execution with
    | stop test _ => simp [readAllTest] at test
    | exit _ step =>
      change Exec host (.read 4096 fun reply => .pure (readAllStep limit _ reply)) _ _ _ _
        at step
      cases step with
      | read_reject capacity _ => exact absurd capacity (by decide)
      | read_return _ _ next => cases next
    | trap _ step =>
      change Exec host (.read 4096 fun reply => .pure (readAllStep limit _ reply)) _ _ _ _
        at step
      cases step with
      | read_reject capacity _ => exact absurd capacity (by decide)
      | read_return _ _ next => cases next
      | read_trap _ operation =>
        obtain ⟨_, _, impossible, _⟩ := streams.read_reply represented operation
        cases impossible
    | next _ step rest =>
      change Exec host (.read 4096 fun reply => .pure (readAllStep limit _ reply)) _ _ _ _
        at step
      cases step with
      | read_reject capacity _ => exact absurd capacity (by decide)
      | @read_return _ _ _ _ after _ _ _ errno committed _ operation next =>
        cases next
        obtain ⟨bytes, nextPosition, replyEq, nextRep, consumed, atEof, sameOutput⟩ :=
          streams.read_reply represented operation
        cases replyEq
        have size := (host.read_bound operation).1
        simp only [Transfer.committed, UInt64.reduceToNat] at size
        by_cases empty : committed.data.size = 0
        · rw [readAllStep_ended empty] at rest
          obtain ⟨rfl, rfl, rfl⟩ := readAll_done rfl rest
          have noInput := atEof empty
          have nextInput : nextPosition.input = [] := by
            rw [noInput] at consumed
            exact (List.append_eq_nil_iff.mp consumed.symm).2
          refine ⟨_, nextPosition, rfl, nextRep, rfl, ?_, sameOutput, Or.inl nextInput⟩
          dsimp only
          rw [split, noInput, nextInput]
        · rw [readAllStep_appended empty] at rest
          have total' : total = byteWords (appendBytes held committed) ++ nextPosition.input := by
            rw [split, consumed, byteWords_appendBytes, List.append_assoc]
          by_cases above : limit.toNat < held.data.size + committed.data.size
          · simp only [above, decide_true] at rest
            obtain ⟨rfl, rfl, rfl⟩ := readAll_done rfl rest
            refine ⟨_, nextPosition, rfl, nextRep, rfl, total', sameOutput, Or.inr ?_⟩
            simp only [appendBytes_size]
            exact above
          · simp only [above, decide_false] at rest
            obtain ⟨result, next, same, nextRep', errno, split', output, ended⟩ :=
              readAllLoop_stream streams total remaining (index + 1) (appendBytes held committed)
                nextPosition nextRep total' (by simp only [appendBytes_size]; omega)
                (by simp only [appendBytes_size]; omega) rest
            exact ⟨result, next, same, nextRep', errno, split', output.trans sameOutput, ended⟩

/-- Every run of `readAll limit`, for a limit with room for its buffer, returns errno 0 and a
prefix of the unread input, keeps the output, and reads to EOF or returns more than `limit`
bytes. -/
theorem StreamHost.readAll {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep) {limit : UInt64}
    (small : limit.toNat < 4294963200) {position : StreamPosition}
    {world trace outcome final} (represented : rep position world)
    (execution : Exec host (LeanExe.Wasi.readAll limit) world trace outcome final) :
    ReadAllReturns rep limit position.input position outcome final := by
  simp only [LeanExe.Wasi.readAll, small, ↓reduceIte] at execution
  cases execution with
  | loop execution =>
    have count : (UInt64.ofNat (limit.toNat + 2)).toNat = limit.toNat + 2 :=
      UInt64.toNat_ofNat_of_lt' (by
        rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    rw [count] at execution
    exact readAllLoop_stream streams position.input _ 0 Bytes.empty position represented
      (by simp) (Nat.zero_le _) (by simp) execution

/-- An input of at most `limit` bytes comes back whole, at EOF. -/
theorem StreamHost.readAll_whole {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep) {limit : UInt64}
    (small : limit.toNat < 4294963200) {position : StreamPosition}
    (size : position.input.length ≤ limit.toNat)
    {world trace outcome final} (represented : rep position world)
    (execution : Exec host (LeanExe.Wasi.readAll limit) world trace outcome final) :
    ∃ result next, outcome = .returned result ∧ rep next final ∧ result.errno = 0 ∧
      byteWords result.bytes = position.input ∧ next.input = [] ∧
      next.output = position.output := by
  obtain ⟨result, next, same, nextRep, errno, split, output, ended⟩ :=
    streams.readAll small represented execution
  have length := congrArg List.length split
  simp only [List.length_append, byteWords_length] at length
  have nextInput : next.input = [] := by
    rcases ended with empty | above
    · exact empty
    · omega
  refine ⟨result, next, same, nextRep, errno, ?_, nextInput, output⟩
  rw [split, nextInput, List.append_nil]

/-- An input of more than `limit` bytes gives more than `limit` bytes. -/
theorem StreamHost.readAll_long {World : Type} {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep) {limit : UInt64}
    (small : limit.toNat < 4294963200) {position : StreamPosition}
    (size : limit.toNat < position.input.length)
    {world trace outcome final} (represented : rep position world)
    (execution : Exec host (LeanExe.Wasi.readAll limit) world trace outcome final) :
    ∃ result next, outcome = .returned result ∧ rep next final ∧ result.errno = 0 ∧
      limit.toNat < result.bytes.data.size ∧ next.output = position.output := by
  obtain ⟨result, next, same, nextRep, errno, split, output, ended⟩ :=
    streams.readAll small represented execution
  refine ⟨result, next, same, nextRep, errno, ?_, output⟩
  rcases ended with empty | above
  · have length := congrArg List.length split
    simp only [List.length_append, byteWords_length, empty, List.length_nil] at length
    omega
  · exact above

end Demos.StreamFold
