import LeanExe.Wasi.CallTable
import Verified.Wasi.HostSpec

/-! Kernel tests of the strides of `poll_oneoff` with two subscriptions.  The expected values are
written from the witx layout of the pinned witx: a `$subscription` is 48 bytes at alignment 8,
`userdata` (`u64`) at 0, the union's tag (`u8`) at 8, and its payload at 16, where `fd_read`'s
`file_descriptor` (`u32`) lies at 16 and the clock's `id` (`u32`), `timeout` (`u64`),
`precision` (`u64`), and `flags` (`u16`) at 16, 24, 32, and 40; an `$event` is 32 bytes at
alignment 8.  The tests state, for `Call.pollOneoffRead`, whose second record is the clock, the
offsets of the fields placed in one array, the length and some bytes of the subscriptions, the
events region of the request, and the sizes that `outputSizesOf` and `replyFitsOf` give the reply.
-/

namespace PollLayoutTest

open LeanExe LeanExe.Wasi Verified.Wasi

/-- The records of `Call.pollOneoffRead`. -/
def records : List (List Field) := [
  [⟨0, 8, .const 1⟩, ⟨8, 1, .const 1⟩, ⟨16, 4, .handle⟩],
  [⟨0, 8, .const 2⟩, ⟨8, 1, .const 0⟩, ⟨16, 4, .word⟩, ⟨24, 8, .word⟩, ⟨32, 8, .const 0⟩,
    ⟨40, 2, .const 0⟩]]

example : Call.pollOneoffRead.params = [.subscriptions records, .result32] := by decide +kernel

/-- The arguments: descriptor 7, clock 1, and a timeout of 1,000 ns. -/
def args : List Arg := [.word 7, .word 1, .word 1000]

/-- The second record starts at byte 48, so its fields lie at 48 plus their witx offsets. -/
example : (placedFields 0 records).map (·.offset) = [0, 8, 16, 48, 56, 64, 72, 80, 88] := by
  decide +kernel

example : (subscriptionBytes records args).data.size = 96 := by decide +kernel

/-- The userdata of each record, the tag of each union, the descriptor, the clock id, and the low
two bytes of the timeout. -/
example : [0, 8, 16, 48, 56, 64, 72, 73].map
    (fun index => (subscriptionBytes records args).data[index]!) =
      [1, 1, 7, 2, 0, 1, 0xe8, 0x03] := by
  decide +kernel

/-- With the subscriptions at 512 and the events at 1024, the events region holds two events of
32 bytes at alignment 8, and the result word lies at 2048. -/
example : (outputRegions Call.pollOneoffRead.params [] args [512, 1024, 2048]).map
    (fun region => (region.pointer, region.size, region.align, region.shown)) =
      [(1024, 64, 8, true), (2048, 4, 4, true)] := by
  decide +kernel

example : outputSizesOf Call.pollOneoffRead.params [] args = [64, 4] := by decide +kernel

/-- Bytes of `size` zeros. -/
def zeros (size : Nat) : Bytes := ⟨⟨Array.replicate size 0⟩⟩

example : replyFitsOf Call.pollOneoffRead.params args [zeros 64, zeros 4] = true := by
  decide +kernel

example : replyFitsOf Call.pollOneoffRead.params args [zeros 32, zeros 4] = false := by
  decide +kernel

example : replyFitsOf Call.pollOneoffRead.params args [zeros 96, zeros 4] = false := by
  decide +kernel

end PollLayoutTest
