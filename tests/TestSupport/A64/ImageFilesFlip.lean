import TestSupport.A64.Flip
import LeanExe.A64.File

/-!
The theorems of the arm64 Image that `a64-uart emit` writes for `flip`, a function over bytes
that reads its message from the UART.  `tests/baremetal/a64-uart.sh` elaborates this file in the
directory of the Image, so `file_nat%` and `file_size%` read flip.img, and no build target includes
it.  The kernel evaluates `genBytesImage` on `flip`'s entry of `Flip.compiled.module`, `inMax`, the
stack's room, and the cap at `imageBase`, and checks that the image's bytes are the file's.
`flip_runs`, the program's theorem in the form `BytesRuns`, then joins with `image_bytes_run_at`,
so each theorem holds for the file's bytes at every base `B` that is a multiple of 4096, with the
image's memory, `flipMemSize` bytes from `B`, in the RAM GiB.  From a boot state whose memory holds
the file's bytes at `B`, with the program counter there, the MMU off, and the UART's receiver at its
first read with no poll done, `flip_uart` states that when the receiver delivers the eight bytes of
the length of a message `msg` of at most `inMax` bytes, the lowest first, and `msg`, with no error
flag, the machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store to the UART
complete, and the UART's output extended by `msg` with bit 5 of each byte flipped and the status 0.
`flip_uart_over` states that for a length above `inMax` the output is extended by the status 64
alone, and `flip_uart_flag` that when byte `j` that the program reads carries an error flag and no
byte before it does, by the status 65 alone.
-/

namespace TestSupport.A64.ImageFilesFlip

open LeanExe.A64 TestSupport.A64 TestSupport.A64.Flip

def flipBytes : Nat := file_nat% "flip.img"
def flipSize : Nat := file_size% "flip.img"

/-- The number of the program's instructions in the image. -/
def flipLength : Nat := imageBytesProgLength compiled.module entry inMax room flipCap imageBase

/-- The bytes of memory that the image uses from its start, the size in its header. -/
def flipMemSize : Nat := imageBytesSize compiled.module entry inMax room flipCap imageBase

set_option maxRecDepth 100000

theorem flip_file : bytesOk (genBytesImage compiled.module entry inMax room flipCap imageBase)
    flipBytes flipSize = true := by decide +kernel

theorem flip_uart (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + flipMemSize ≤ 0x80000000)
    (hm : ∀ j < flipSize, b.core.mem (B + UInt64.ofNat j) = byteAt flipBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (msg : List UInt8)
    (hlen : msg.length ≤ inMax.toNat)
    (hd : h.rx.Delivers (bytesOf (UInt64.ofNat msg.length) ++ msg)) :
    ∃ b', BootReach h (protectedBytes B flipLength)
        (fetchFrom b.core.mem B (codeWords flipLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords flipLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ msg.map (· ^^^ 32) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := (image_bytes_run_at h flip_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff hio flip_runs).1 msg hlen hd
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem flip_uart_over (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + flipMemSize ≤ 0x80000000)
    (hm : ∀ j < flipSize, b.core.mem (B + UInt64.ofNat j) = byteAt flipBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (L : UInt64) (hL : inMax < L)
    (hd : h.rx.Delivers (bytesOf L)) :
    ∃ b', BootReach h (protectedBytes B flipLength)
        (fetchFrom b.core.mem B (codeWords flipLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords flipLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [64] :=
  (image_bytes_run_at h flip_file (by decide) (by decide) (by decide) hB hlo hhi hm hpc hoff hio
    flip_runs).2.1 L hL hd

theorem flip_uart_flag (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + flipMemSize ≤ 0x80000000)
    (hm : ∀ j < flipSize, b.core.mem (B + UInt64.ofNat j) = byteAt flipBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (j : Nat)
    (hpre : ∀ i < j, ¬ h.rx.Flagged i) (hf : h.rx.Flagged j)
    (hj : j < 8 ∨ (rxSum h.rx 0 8 ≤ inMax.toNat ∧ j < 8 + rxSum h.rx 0 8)) :
    ∃ b', BootReach h (protectedBytes B flipLength)
        (fetchFrom b.core.mem B (codeWords flipLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords flipLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65] :=
  (image_bytes_run_at h flip_file (by decide) (by decide) (by decide) hB hlo hhi hm hpc hoff hio
    flip_runs).2.2 j hpre hf hj

#print axioms flip_file
#print axioms flip_uart
#print axioms flip_uart_over
#print axioms flip_uart_flag

end TestSupport.A64.ImageFilesFlip
