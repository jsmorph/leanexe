import TestSupport.A64.Uart
import LeanExe.A64.File

/-!
The theorems of the arm64 Image that `a64-uart emit` writes, GCD's loop on two words read from the
UART.  `tests/baremetal/a64-uart.sh` elaborates this file in the directory of the Image, so
`file_nat%` and `file_size%` read gcduart.img, and no build target includes it.  The kernel
evaluates `genInImage` on entry 2 of `loopCompiled.module`, two words, the stack's room, the cap,
and the form of the result at `imageBase`, and checks that the image's bytes are the file's.
`uart_runs`, the program's theorem in the form `InputRuns`, then joins with `image_input_run`.
From a boot state whose memory holds the file's bytes at `imageBase`, with the program counter
there, the MMU off, and the UART's receiver at its first read with no poll done, `gcd_uart` states
that when the receiver delivers the sixteen bytes of two words `x` and `y`, each word's lowest byte
first and no byte with an error flag, the machine reaches `HVC #0` with X0 holding PSCI's
`SYSTEM_OFF`, every store to the UART complete, and the UART's output extended by the eight bytes
of `gcd x y` and the status 0.  `gcd_uart_flag` states that when byte `j` of the first sixteen
carries an error flag and no byte before it does, the output is extended by the status 65 alone.
`gcd_uart_at` and `gcd_uart_flag_at` state the same of the file's bytes at every base `B` that is
a multiple of 4096, with the image's memory, `gcdUartMemSize` bytes from `B`, in the RAM GiB, from
`image_input_run_at`.
-/

namespace TestSupport.A64.ImageFilesUart

open LeanExe.A64 TestSupport.A64 TestSupport.Native.Gcd

def gcdUartBytes : Nat := file_nat% "gcduart.img"
def gcdUartSize : Nat := file_size% "gcduart.img"

def gcdUartLength : Nat := imageInProgLength loopCompiled.module 2 2 room cap .word imageBase

set_option maxRecDepth 100000

theorem gcduart_file : bytesOk (genInImage loopCompiled.module 2 2 room cap .word imageBase)
    gcdUartBytes gcdUartSize = true := by decide +kernel

theorem gcd_uart (h : Hw) (b : Boot)
    (hm : ∀ j < gcdUartSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt gcdUartBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (x y : UInt64)
    (hd : h.rx.Delivers (bytesOf x ++ bytesOf y)) :
    ∃ b', BootReach h (protectedBytes imageBase gcdUartLength)
        (fetchFrom b.core.mem imageBase (codeWords gcdUartLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords gcdUartLength) b'.core.pc =
        some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord (gcd x y) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := (image_input_run h gcduart_file (by decide) (by decide)
    (by decide) hm hpc hoff hio (Uart.uart_runs room cap)).1 [x, y] rfl
    (by show h.rx.Delivers (bytesOf x ++ (bytesOf y ++ [])); rw [List.append_nil]; exact hd)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem gcd_uart_flag (h : Hw) (b : Boot)
    (hm : ∀ j < gcdUartSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt gcdUartBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (j : Nat) (hj : j < 16)
    (hpre : ∀ i < j, ¬ h.rx.Flagged i) (hf : h.rx.Flagged j) :
    ∃ b', BootReach h (protectedBytes imageBase gcdUartLength)
        (fetchFrom b.core.mem imageBase (codeWords gcdUartLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords gcdUartLength) b'.core.pc =
        some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65] :=
  (image_input_run h gcduart_file (by decide) (by decide) (by decide) hm hpc hoff hio
    (Uart.uart_runs room cap)).2 j hj hpre hf

/-- The bytes of memory that the image uses from its start, the size in its header. -/
def gcdUartMemSize : Nat := imageInSize loopCompiled.module 2 2 room cap .word imageBase

theorem gcd_uart_at (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + gcdUartMemSize ≤ 0x80000000)
    (hm : ∀ j < gcdUartSize, b.core.mem (B + UInt64.ofNat j) = byteAt gcdUartBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (x y : UInt64)
    (hd : h.rx.Delivers (bytesOf x ++ bytesOf y)) :
    ∃ b', BootReach h (protectedBytes B gcdUartLength)
        (fetchFrom b.core.mem B (codeWords gcdUartLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords gcdUartLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord (gcd x y) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := (image_input_run_at h gcduart_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff hio (Uart.uart_runs room cap)).1 [x, y] rfl
    (by show h.rx.Delivers (bytesOf x ++ (bytesOf y ++ [])); rw [List.append_nil]; exact hd)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem gcd_uart_flag_at (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + gcdUartMemSize ≤ 0x80000000)
    (hm : ∀ j < gcdUartSize, b.core.mem (B + UInt64.ofNat j) = byteAt gcdUartBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (j : Nat) (hj : j < 16)
    (hpre : ∀ i < j, ¬ h.rx.Flagged i) (hf : h.rx.Flagged j) :
    ∃ b', BootReach h (protectedBytes B gcdUartLength)
        (fetchFrom b.core.mem B (codeWords gcdUartLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords gcdUartLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65] :=
  (image_input_run_at h gcduart_file (by decide) (by decide) (by decide) hB hlo hhi hm hpc hoff
    hio (Uart.uart_runs room cap)).2 j hj hpre hf

#print axioms gcduart_file
#print axioms gcd_uart
#print axioms gcd_uart_flag
#print axioms gcd_uart_at
#print axioms gcd_uart_flag_at

end TestSupport.A64.ImageFilesUart
