import TestSupport.A64.Programs
import TestSupport.A64.Exp
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the exponential's arm64 Images, `exp1.img` and `expsub.img`, which
`a64-programs emit` writes.  `tests/baremetal/a64-images.sh` elaborates this file in the directory
of the Images, as it does `tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.
The kernel evaluates `genImage` on entry 5 of `Exp.compiled.module`, `Exp.exp`, and the word of 1
or of -740 at `imageBase` and checks that the image's bytes are the file's.  `TestSupport.A64.Exp.runs`
then joins with `image_run_at`: for every base `B` that is a multiple of 4096 and whose image's
memory lies in the RAM GiB, from a boot state whose memory holds the file's bytes at `B`, with the
program counter there and the MMU off, the machine reaches `HVC #0` with X0 holding PSCI's
`SYSTEM_OFF`, every store to the UART complete, and the UART's output extended by the eight bytes
of the word of `Exp.exp x` and the status 0.  `exp1_accuracy` and `expsub_accuracy` add
`ExpTheorem.exp_one_step`: the word that the UART carries is at most that of positive infinity and
lies within one representable step of the nonnegative nearest-even rounding of `e` and of
`exp (-740)`.  The programs run floating-point instructions, comparisons included, whose meanings
in the model are Talos's IEEE 754 functions.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64 Library.Numerics.Float64
open LeanExe.ProofKit.F64PositiveRounding (roundNearestEven)

def exp1Bytes : Nat := file_nat% "exp1.img"
def exp1Size : Nat := file_size% "exp1.img"
def expsubBytes : Nat := file_nat% "expsub.img"
def expsubSize : Nat := file_size% "expsub.img"

def exp1Length : Nat :=
  imageProgLength Exp.compiled.module 5 [0x3FF0000000000000] room cap .word imageBase
def expsubLength : Nat :=
  imageProgLength Exp.compiled.module 5 [0xC087200000000000] room cap .word imageBase

def exp1ImageSize : Nat :=
  imageSize Exp.compiled.module 5 [0x3FF0000000000000] room cap .word imageBase
def expsubImageSize : Nat :=
  imageSize Exp.compiled.module 5 [0xC087200000000000] room cap .word imageBase

set_option maxRecDepth 100000

theorem exp1_file : bytesOk (genImage Exp.compiled.module 5 [0x3FF0000000000000] room cap .word
    imageBase) exp1Bytes exp1Size = true := by decide +kernel

theorem expsub_file : bytesOk (genImage Exp.compiled.module 5 [0xC087200000000000] room cap .word
    imageBase) expsubBytes expsubSize = true := by decide +kernel

theorem one_bits : (Float.ofBits 0x3FF0000000000000).toBits = 0x3FF0000000000000 := by
  rw [LeanExe.ProofKit.F64Bits.toBits_ofBits]
  decide +kernel

theorem m740_bits : (Float.ofBits 0xC087200000000000).toBits = 0xC087200000000000 := by
  rw [LeanExe.ProofKit.F64Bits.toBits_ofBits]
  decide +kernel

/-- The exponential's Image on 1.  From a boot state whose memory holds the file's bytes at `B`,
with the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after
writing to the UART the eight bytes of the word of `Exp.exp 1`, followed by the status byte 0. -/
theorem exp1 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + exp1ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < exp1Size, b.core.mem (B + UInt64.ofNat j) = byteAt exp1Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B exp1Length)
        (fetchFrom b.core.mem B (codeWords exp1Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords exp1Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (Exp.exp (Float.ofBits 0x3FF0000000000000)).toBits ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h exp1_file (by decide) (by decide) (by decide)
    hB hlo hhi hm hpc hoff (Exp.runs _ one_bits room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- The exponential's Image on -740, whose result is subnormal. -/
theorem expsub (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + expsubImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < expsubSize, b.core.mem (B + UInt64.ofNat j) = byteAt expsubBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B expsubLength)
        (fetchFrom b.core.mem B (codeWords expsubLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords expsubLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (Exp.exp (Float.ofBits 0xC087200000000000)).toBits ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h expsub_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff (Exp.runs _ m740_bits room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- The exponential's Image on 1 with the accuracy theorem: the UART carries the eight bytes of a
word `w` and the status 0, and `w` is at most the word of positive infinity and lies within one
representable step of the nonnegative nearest-even rounding of `e`. -/
theorem exp1_accuracy (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + exp1ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < exp1Size, b.core.mem (B + UInt64.ofNat j) = byteAt exp1Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B exp1Length)
        (fetchFrom b.core.mem B (codeWords exp1Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords exp1Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w.toNat ≤ 0x7FF0000000000000 ∧ w.toNat ≤ (roundNearestEven (Real.exp 1)).toNat + 1 ∧
      (roundNearestEven (Real.exp 1)).toNat ≤ w.toNat + 1 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := exp1 h B hB hlo hhi b hm hpc hoff
  have ha := Exp.one_step (Float.ofBits 0x3FF0000000000000) 1
    (by rw [one_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel)
    (by rw [one_bits]; exact_mod_cast Exp.value_of_scaled (q := 1) (by decide +kernel))
  exact ⟨b', _, r, hc, hx, hu, ho, ha⟩

/-- The exponential's Image on -740 with the accuracy theorem: the UART carries the eight bytes of
a word `w` and the status 0, and `w` is at most the word of positive infinity and lies within one
representable step of the nonnegative nearest-even rounding of `exp (-740)`. -/
theorem expsub_accuracy (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + expsubImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < expsubSize, b.core.mem (B + UInt64.ofNat j) = byteAt expsubBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B expsubLength)
        (fetchFrom b.core.mem B (codeWords expsubLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords expsubLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w.toNat ≤ 0x7FF0000000000000 ∧ w.toNat ≤ (roundNearestEven (Real.exp (-740))).toNat + 1 ∧
      (roundNearestEven (Real.exp (-740))).toNat ≤ w.toNat + 1 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := expsub h B hB hlo hhi b hm hpc hoff
  have ha := Exp.one_step (Float.ofBits 0xC087200000000000) (-740)
    (by rw [m740_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel)
    (by rw [m740_bits]; exact_mod_cast Exp.value_of_scaled (q := -740) (by decide +kernel))
  exact ⟨b', _, r, hc, hx, hu, ho, ha⟩

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.exp1
#print axioms TestSupport.A64.ImageFiles.expsub
#print axioms TestSupport.A64.ImageFiles.exp1_accuracy
#print axioms TestSupport.A64.ImageFiles.expsub_accuracy
