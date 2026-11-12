import TestSupport.A64.Mss
import LeanExe.A64.File

/-!
The theorems of the arm64 Image that `a64-uart emit` writes for `mss`, Kadane's maximum segment
sum over the words of a message that the Image reads from the UART.
`tests/baremetal/a64-uart.sh` elaborates this file in the directory of the Image, so `file_nat%`
and `file_size%` read mss.img, and no build target includes it.  The kernel evaluates
`genBytesImage` on `mssBytes`'s entry of `Mss.compiled.module`, `inMax`, the stack's room, and the
cap at `imageBase`, and checks that the image's bytes are the file's.  `mss_runs`, the program's
theorem in the form `BytesRuns`, then joins with `image_bytes_run_at`, so each theorem holds for the
file's bytes at every base `B` that is a multiple of 4096, with the image's memory, `mssMemSize`
bytes from `B`, in the RAM GiB.  From a boot state whose memory holds the file's bytes at `B`, with
the program counter there, the MMU off, and the UART's receiver at its first read with no poll
done, `mss_uart` states that when the receiver delivers the eight bytes of the length of a message
`msg` of at most `inMax` bytes, the lowest first, and `msg`, with no error flag, the machine reaches
`HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store to the UART complete, and the UART's
output extended by `output msg` and the status 0.  `mss_uart_over` states that for a length above
`inMax` the output is extended by the status 64 alone, and `mss_uart_flag` that when byte `j` that
the program reads carries an error flag and no byte before it does, by the status 65 alone.
`mss_uart_spec` states the run with the specification over ℤ.
-/

namespace TestSupport.A64.ImageFilesMss

open LeanExe.A64 TestSupport.A64 TestSupport.A64.Mss

def mssFile : Nat := file_nat% "mss.img"
def mssFileSize : Nat := file_size% "mss.img"

/-- The number of the program's instructions in the image. -/
def mssLength : Nat := imageBytesProgLength compiled.module entry inMax room mssCap imageBase

/-- The bytes of memory that the image uses from its start, the size in its header. -/
def mssMemSize : Nat := imageBytesSize compiled.module entry inMax room mssCap imageBase

set_option maxRecDepth 100000

theorem mss_file : bytesOk (genBytesImage compiled.module entry inMax room mssCap imageBase)
    mssFile mssFileSize = true := by decide +kernel

theorem mss_uart (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + mssMemSize ≤ 0x80000000)
    (hm : ∀ j < mssFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt mssFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (msg : List UInt8)
    (hlen : msg.length ≤ inMax.toNat)
    (hd : h.rx.Delivers (bytesOf (UInt64.ofNat msg.length) ++ msg)) :
    ∃ b', BootReach h (protectedBytes B mssLength)
        (fetchFrom b.core.mem B (codeWords mssLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords mssLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ output msg ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := (image_bytes_run_at h mss_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff hio mss_runs).1 msg hlen hd
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem mss_uart_over (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + mssMemSize ≤ 0x80000000)
    (hm : ∀ j < mssFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt mssFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (L : UInt64) (hL : inMax < L)
    (hd : h.rx.Delivers (bytesOf L)) :
    ∃ b', BootReach h (protectedBytes B mssLength)
        (fetchFrom b.core.mem B (codeWords mssLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords mssLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [64] :=
  (image_bytes_run_at h mss_file (by decide) (by decide) (by decide) hB hlo hhi hm hpc hoff hio
    mss_runs).2.1 L hL hd

theorem mss_uart_flag (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + mssMemSize ≤ 0x80000000)
    (hm : ∀ j < mssFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt mssFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (j : Nat)
    (hpre : ∀ i < j, ¬ h.rx.Flagged i) (hf : h.rx.Flagged j)
    (hj : j < 8 ∨ (rxSum h.rx 0 8 ≤ inMax.toNat ∧ j < 8 + rxSum h.rx 0 8)) :
    ∃ b', BootReach h (protectedBytes B mssLength)
        (fetchFrom b.core.mem B (codeWords mssLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords mssLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65] :=
  (image_bytes_run_at h mss_file (by decide) (by decide) (by decide) hB hlo hhi hm hpc hoff hio
    mss_runs).2.2 j hpre hf hj

/-- The maximum segment sum's Image computes the specification over ℤ.  From a boot state whose
memory holds the file's bytes at `B`, with the program counter there, the MMU off, and the UART's
receiver at its first read with no poll done, let the receiver deliver, with no error flag, the
eight bytes of the length `8 n`, the lowest first, and then the eight bytes of each of `n` words
`ws`, the lowest first, where `8 n` is at most 8,800,000 and the absolute values of the words, read
as signed 64-bit integers, sum to less than `2^63`.  Every message of `8 n` bytes is the bytes of
such a list of words.  Then the machine reaches PSCI's `SYSTEM_OFF` after writing to the UART the
eight bytes of a word `y`, the lowest first, and the status byte 0.  The word `y`, read as a signed
64-bit integer, is the greatest sum of a segment of the words read as integers, from 0 for the
empty segment, as `maxSegmentSum` of `Library/Arrays/MaxSegmentSum/Spec.lean` defines it. -/
theorem mss_uart_spec (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + mssMemSize ≤ 0x80000000)
    (hm : ∀ j < mssFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt mssFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (ws : List Int64)
    (hlen : 8 * ws.length ≤ 8800000) (hsum : (ws.map fun w => w.toInt.natAbs).sum < 2 ^ 63)
    (hd : h.rx.Delivers
      (bytesOf (UInt64.ofNat (8 * ws.length)) ++ (ws.map Int64.toUInt64).flatMap bytesOf)) :
    ∃ (b' : Boot) (y : Int64), BootReach h (protectedBytes B mssLength)
        (fetchFrom b.core.mem B (codeWords mssLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords mssLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ bytesOf y.toUInt64 ++ [0] ∧
      y.toInt = Library.Arrays.MaxSegmentSum.maxSegmentSum (ws.map Int64.toInt) := by
  have hl : ((ws.map Int64.toUInt64).flatMap bytesOf).length = 8 * ws.length := by
    rw [length_flatMap_bytesOf, List.length_map]
  obtain ⟨y, hy, hspec⟩ := output_spec ws (by omega) hsum
  obtain ⟨b', r, hc, hx, hu, ho⟩ := mss_uart h b B hB hlo hhi hm hpc hoff hio _
    (by rw [hl]; exact Nat.le_trans hlen (by decide)) (by rw [hl]; exact hd)
  refine ⟨b', y, r, hc, hx, hu, ?_, hspec⟩
  rw [ho, hy]

#print axioms mss_file
#print axioms mss_uart
#print axioms mss_uart_over
#print axioms mss_uart_flag
#print axioms mss_uart_spec

end TestSupport.A64.ImageFilesMss
