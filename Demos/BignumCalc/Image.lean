module

public import Demos.BignumCalc.BytesBare
public import LeanExe.A64.File

@[expose] public section

/-!
# The theorems of the calculator's AArch64 Image

The Image reads a message from the UART, runs `calcBytes` on it, and writes the message's line.
`tests/bignum-calc/image.sh` writes the Image to `build/bignum-calc/image/bignum-calc.img` and, with
`--check`, elaborates this file in the directory of the Image, so that `file_nat%` and `file_size%`
read `bignum-calc.img`, and no build target includes it.  The kernel evaluates `genBytesImage` on
`calcBytes`'s entry of `messageCompiled.module`, `imageMax`, the stack's room, and the cap at
`imageBase`, and checks that the Image's bytes are the file's (`calc_file_image`).  `calc_runs`, the program's theorem in the
form `BytesRuns`, then joins with `image_bytes_run_at`, so each theorem holds for the file's bytes
at every base `B` that is a multiple of 4096, with the Image's memory, `calcMemSize` bytes from `B`,
in the RAM GiB.

`calc_mem_size` and `calc_fits` state that the Image's memory, 34,193,424 bytes, fits the RAM GiB
from `imageBase`, so the premise on the base can hold.

Each theorem starts from a boot state whose memory holds the file's bytes at `B`, with the program
counter there, the MMU off, and the UART's receiver at its first read with no poll done, and ends
at `HVC #0` with X0 holding PSCI's `SYSTEM_OFF` and every store to the UART complete.  The Image's
last byte is its exit status.  `calc_uart` states that when the receiver delivers the eight bytes
of the length of a message `msg` of at most 65,536 bytes, the lowest first, and `msg`, with no
error flag, the UART's output is extended by `calcSpec msg`, the message's line, and the exit status
byte 0.  `calc_uart_unary`, `calc_uart_binary`, and `calc_uart_zero_divisor` join the Image with the
main claims: for a message that names an operation and gives Lean's texts of integers, the UART
receives `0`, a space, and Lean's text of the exact result, or `3` for a division by zero, and then
the exit status byte 0.  `calc_uart_over` states that a length above 65,536 gives the exit status 64
alone, and `calc_uart_flag` that when byte `j` that the program reads carries an error flag and no
byte before it does, the output is the exit status 65 alone.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open LeanExe.A64
open Library.Numerics.Decimal.Shared.StrconvGrammar (ascii)

def calcFile : Nat := file_nat% "bignum-calc.img"
def calcFileSize : Nat := file_size% "bignum-calc.img"

/-- The number of the program's instructions in the Image. -/
def calcLength : Nat :=
  imageBytesProgLength messageCompiled.module imageEntry imageMax imageRoom imageCap imageBase

/-- The bytes of memory that the Image uses from its start, the size in its header. -/
def calcMemSize : Nat :=
  imageBytesSize messageCompiled.module imageEntry imageMax imageRoom imageCap imageBase

set_option maxRecDepth 100000

/-- The Image uses 34,193,424 bytes of memory from its start. -/
theorem calc_mem_size : calcMemSize = 34193424 := by decide +kernel

/-- The Image's memory fits the RAM GiB from `imageBase`, so the theorems' premise on the base
holds at `imageBase`. -/
theorem calc_fits : imageBase.toNat % 4096 = 0 ∧ 0x40000000 ≤ imageBase.toNat ∧
    imageBase.toNat + calcMemSize ≤ 0x80000000 := by
  rw [calc_mem_size]; decide

/-- The file `bignum-calc.img` holds the bytes that `genBytesImage` gives for the
entry `calcBytes` of `messageCompiled.module`, `imageMax`, the stack's room, and the cap at
`imageBase`. -/
theorem calc_file_image : bytesOk (genBytesImage messageCompiled.module imageEntry imageMax
    imageRoom imageCap imageBase) calcFile calcFileSize = true := by decide +kernel

/-- When the receiver delivers the length of a message `msg` of at most 65,536 bytes and `msg`,
with no error flag, the machine reaches `SYSTEM_OFF` after writing the message's line and the exit
status byte 0. -/
theorem calc_uart (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + calcMemSize ≤ 0x80000000)
    (hm : ∀ j < calcFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt calcFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (msg : List UInt8)
    (hlen : msg.length ≤ 65536)
    (hd : h.rx.Delivers (bytesOf (UInt64.ofNat msg.length) ++ msg)) :
    ∃ b', BootReach h (protectedBytes B calcLength)
        (fetchFrom b.core.mem B (codeWords calcLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords calcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ calcSpec msg ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := (image_bytes_run_at h calc_file_image (by decide)
    (by decide) (by decide) hB hlo hhi hm hpc hoff hio calc_runs).1 msg hlen hd
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, by rw [ho, output_eq msg hlen]⟩
  · exact hf.elim

/-- A delivered message `neg a`, for Lean's text of an integer `a`, gives `0`, a space, and Lean's
text of `-a`, and the exit status 0. -/
theorem calc_uart_unary (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + calcMemSize ≤ 0x80000000)
    (hm : ∀ j < calcFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt calcFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (x : ℤ)
    (hlen : (ascii ("neg " ++ toString x)).length ≤ 65536)
    (hd : h.rx.Delivers (bytesOf (UInt64.ofNat (ascii ("neg " ++ toString x)).length) ++
      ascii ("neg " ++ toString x))) :
    ∃ b', BootReach h (protectedBytes B calcLength)
        (fetchFrom b.core.mem B (codeWords calcLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords calcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ ascii ("0 " ++ toString (-x)) ++ [0] := by
  obtain ⟨b', rr, hc, hx, hu, ho⟩ := calc_uart h b B hB hlo hhi hm hpc hoff hio _ hlen hd
  exact ⟨b', rr, hc, hx, hu, by rw [ho, calcSpec_unary x hlen]⟩

/-- A delivered message `name a b`, for a binary operation of `binaryOps` and Lean's texts of
integers `a` and `b`, gives `0`, a space, and Lean's text of the operation's exact result, unless
the operation divides and `b` is 0, and the exit status 0. -/
theorem calc_uart_binary (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + calcMemSize ≤ 0x80000000)
    (hm : ∀ j < calcFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt calcFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (name : String) (division : Bool)
    (f : ℤ → ℤ → ℤ) (hop : (name, division, f) ∈ binaryOps) (x y : ℤ)
    (hdiv : ¬ (division = true ∧ y = 0))
    (hlen : (ascii (name ++ " " ++ toString x ++ " " ++ toString y)).length ≤ 65536)
    (hd : h.rx.Delivers (bytesOf (UInt64.ofNat
      (ascii (name ++ " " ++ toString x ++ " " ++ toString y)).length) ++
      ascii (name ++ " " ++ toString x ++ " " ++ toString y))) :
    ∃ b', BootReach h (protectedBytes B calcLength)
        (fetchFrom b.core.mem B (codeWords calcLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords calcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ ascii ("0 " ++ toString (f x y)) ++ [0] := by
  obtain ⟨b', rr, hc, hx, hu, ho⟩ := calc_uart h b B hB hlo hhi hm hpc hoff hio _ hlen hd
  exact ⟨b', rr, hc, hx, hu, by rw [ho, calcSpec_binary name division f hop x y hdiv hlen]⟩

/-- A delivered message `name a 0`, for a division of `binaryOps` and Lean's text of an integer
`a`, gives `3`, and the exit status 0. -/
theorem calc_uart_zero_divisor (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + calcMemSize ≤ 0x80000000)
    (hm : ∀ j < calcFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt calcFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (name : String) (f : ℤ → ℤ → ℤ)
    (hop : (name, true, f) ∈ binaryOps) (x : ℤ)
    (hlen : (ascii (name ++ " " ++ toString x ++ " 0")).length ≤ 65536)
    (hd : h.rx.Delivers (bytesOf (UInt64.ofNat (ascii (name ++ " " ++ toString x ++ " 0")).length) ++
      ascii (name ++ " " ++ toString x ++ " 0"))) :
    ∃ b', BootReach h (protectedBytes B calcLength)
        (fetchFrom b.core.mem B (codeWords calcLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords calcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ ascii "3" ++ [0] := by
  obtain ⟨b', rr, hc, hx, hu, ho⟩ := calc_uart h b B hB hlo hhi hm hpc hoff hio _ hlen hd
  exact ⟨b', rr, hc, hx, hu, by rw [ho, calcSpec_zero_divisor name f hop x hlen]⟩

/-- A delivered length above 65,536 gives the exit status 64 alone. -/
theorem calc_uart_over (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + calcMemSize ≤ 0x80000000)
    (hm : ∀ j < calcFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt calcFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (L : UInt64) (hL : 65536 < L)
    (hd : h.rx.Delivers (bytesOf L)) :
    ∃ b', BootReach h (protectedBytes B calcLength)
        (fetchFrom b.core.mem B (codeWords calcLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords calcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [64] :=
  (image_bytes_run_at h calc_file_image (by decide) (by decide) (by decide) hB hlo hhi hm
    hpc hoff hio calc_runs).2.1 L hL hd

/-- When byte `j` that the program reads carries an error flag and no byte before it does, the
machine writes the exit status 65 alone. -/
theorem calc_uart_flag (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + calcMemSize ≤ 0x80000000)
    (hm : ∀ j < calcFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt calcFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (j : Nat)
    (hpre : ∀ i < j, ¬ h.rx.Flagged i) (hf : h.rx.Flagged j)
    (hj : j < 8 ∨ (rxSum h.rx 0 8 ≤ 65536 ∧ j < 8 + rxSum h.rx 0 8)) :
    ∃ b', BootReach h (protectedBytes B calcLength)
        (fetchFrom b.core.mem B (codeWords calcLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords calcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧ b'.core.out = b.core.out ++ [65] :=
  (image_bytes_run_at h calc_file_image (by decide) (by decide) (by decide) hB hlo hhi hm
    hpc hoff hio calc_runs).2.2 j hpre hf hj

#print axioms calc_mem_size
#print axioms calc_fits
#print axioms calc_file_image
#print axioms calc_uart
#print axioms calc_uart_unary
#print axioms calc_uart_binary
#print axioms calc_uart_zero_divisor
#print axioms calc_uart_over
#print axioms calc_uart_flag
#print axioms output_eq
#print axioms calc_runs

end Demos.BignumCalc
