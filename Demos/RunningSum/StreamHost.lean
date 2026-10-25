import Demos.RunningSum.StreamBytes
import Demos.RunningSum.TerminationHost

namespace Demos.RunningSum

open LeanExe LeanExe.Wasi

structure StreamPosition where
  input : List UInt64
  output : List UInt64
  zeroWrites : Nat

structure StreamHost (host : Host World) (rep : StreamPosition → World → Prop) : Prop where
  read_available : ∀ position world, rep position world →
    ∃ bytes final, host.read world 4096 (.returned 0 bytes) final
  write_available : ∀ position world bytes, rep position world → 0 < bytes.data.size →
    ∃ count final, host.write world .stdout bytes (.returned 0 count) final
  read_reply : ∀ {position world reply final}, rep position world →
    host.read world 4096 reply final →
    ∃ bytes next, reply = .returned 0 bytes ∧ rep next final ∧
      position.input = byteWords bytes ++ next.input ∧
      (bytes.data.size = 0 → position.input = []) ∧ next.output = position.output
  write_reply : ∀ {position world bytes reply final}, rep position world →
    0 < bytes.data.size → host.write world .stdout bytes reply final →
    ∃ count next, reply = .returned 0 count ∧ rep next final ∧
      next.input = position.input ∧
      next.output = position.output ++ (byteWords bytes).take count.toNat ∧
      (count = 0 → next.zeroWrites < position.zeroWrites)

theorem StreamHost.progress {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) :
    Termination.StreamProgress host rep (fun position => position.input.length)
      StreamPosition.zeroWrites := by
  refine ⟨streams.read_available, streams.write_available, ?_, ?_⟩
  · intro position world reply final represented operation
    obtain ⟨bytes, next, replyEq, nextRep, consumed, _, _⟩ :=
      streams.read_reply represented operation
    have length := congrArg List.length consumed
    simp only [List.length_append, byteWords_length] at length
    exact ⟨bytes, next, replyEq, nextRep, by omega, by intro nonempty; omega⟩
  · intro position world bytes reply final represented nonempty operation
    obtain ⟨count, next, replyEq, nextRep, same, _, decreased⟩ :=
      streams.write_reply represented nonempty operation
    exact ⟨count, next, replyEq, nextRep, congrArg List.length same, decreased⟩

theorem StreamHost.read_empty {host : Host World} {rep : StreamPosition → World → Prop}
    (streams : StreamHost host rep) {position : StreamPosition} {world final : World}
    {bytes : Bytes} (represented : rep position world)
    (operation : host.read world 4096 (.returned 0 bytes) final)
    (empty : bytes.data.size = 0) : position.input = [] := by
  obtain ⟨actual, next, same, _, _, eof, _⟩ := streams.read_reply represented operation
  cases same
  exact eof empty

theorem StreamHost.read_after_eof {host : Host World}
    {rep : StreamPosition → World → Prop} (streams : StreamHost host rep)
    {position : StreamPosition} {world final : World} {bytes : Bytes}
    (represented : rep position world) (operation : host.read world 4096 (.returned 0 bytes) final)
    (empty : position.input = []) : bytes.data.size = 0 := by
  obtain ⟨actual, next, same, _, consumed, _, _⟩ := streams.read_reply represented operation
  cases same
  have length := congrArg List.length consumed
  simp only [empty, List.length_nil, List.length_append, byteWords_length] at length
  omega

end Demos.RunningSum
