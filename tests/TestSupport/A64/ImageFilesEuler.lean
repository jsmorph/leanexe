import TestSupport.A64.Programs
import TestSupport.A64.Euler
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorem of the Euler solver's arm64 Image, `euler.img`, which `a64-programs emit` writes.
`tests/baremetal/a64-images.sh` elaborates this file in the directory of the Images, as it does
`tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.  The kernel evaluates
`genImage` on entry 28 of `Demos.Euler.Verified.compiled.module` and the argument 4 at
`imageBase` and checks that the image's bytes are the file's.  `TestSupport.A64.Euler.runs` then
joins with `image_run_at`: for every base `B` that is a multiple of 4096 and whose image's memory
lies in the RAM GiB, from a boot state whose memory holds the file's bytes at `B`, with the program
counter there and the MMU off, the machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`,
every store to the UART complete, and the UART's output extended by the encoding of the array
`Demos.Euler.Buffered.solve 4` and the status 0.  The program runs floating-point instructions,
whose meanings in the model are Talos's IEEE 754 functions.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64

def eulerBytes : Nat := file_nat% "euler.img"
def eulerSize : Nat := file_size% "euler.img"

def eulerLength : Nat :=
  imageProgLength Demos.Euler.Verified.compiled.module 28 [4] room cap .array imageBase

def eulerImageSize : Nat :=
  imageSize Demos.Euler.Verified.compiled.module 28 [4] room cap .array imageBase

set_option maxRecDepth 100000

theorem euler_file : bytesOk (genImage Demos.Euler.Verified.compiled.module 28 [4] room cap .array
    imageBase) eulerBytes eulerSize = true := by decide +kernel

/-- The Euler solver's Image.  From a boot state whose memory holds the file's bytes at `B`, with
the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after writing to
the UART the encoding of the array `Demos.Euler.Buffered.solve 4`, its length word and its
elements, followed by the status byte 0. -/
theorem euler (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + eulerImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < eulerSize, b.core.mem (B + UInt64.ofNat j) = byteAt eulerBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B eulerLength)
        (fetchFrom b.core.mem B (codeWords eulerLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords eulerLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray (Demos.Euler.Buffered.solve 4) ++
        [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h euler_file (by decide) (by decide) (by decide)
    hB hlo hhi hm hpc hoff (Euler.runs room cap (by decide +kernel))
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.euler
