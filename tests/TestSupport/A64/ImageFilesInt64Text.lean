import TestSupport.A64.Programs
import TestSupport.A64.Int64Text
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the arm64 Image of `Library.Numerics.Decimal.Int64Text`, `int64min.img`, which
`a64-programs emit` writes.  `tests/baremetal/a64-images.sh` elaborates this file in the directory
of the Images, as it does `tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.
The kernel evaluates `genImage` on entry 4 of `Library.Numerics.Decimal.Int64Text.compiled.module`,
`printInt64`, at the word of `Int64.minValue`, and checks that the image's bytes are the file's.
`TestSupport.A64.Int64Text.printInt64_runs` then joins with `image_run_at`: for every base `B` that
is a multiple of 4096 and whose image's memory lies in the RAM GiB, from a boot state whose memory
holds the file's bytes at `B`, with the program counter there and the MMU off, the machine reaches
`HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store to the UART complete, and the UART's
output extended by the encoding of the text's array and the status 0.  `int64min_image_spec` adds
the specification: the array is `expectedPrint Int64.minValue`, the words of the 20 bytes of
`-9223372036854775808`.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64 Library.Numerics.Decimal.Int64Text

def int64minBytes : Nat := file_nat% "int64min.img"
def int64minSize : Nat := file_size% "int64min.img"

/-- The word of `minValue`. -/
abbrev wmin64 : UInt64 := 9223372036854775808

def int64minLength : Nat := imageProgLength compiled.module 4 [wmin64] room cap .array imageBase

def int64minImageSize : Nat := imageSize compiled.module 4 [wmin64] room cap .array imageBase

set_option maxRecDepth 100000

theorem int64min_file : bytesOk (genImage compiled.module 4 [wmin64] room cap .array imageBase)
    int64minBytes int64minSize = true := by decide +kernel

/-- `printInt64 minValue`'s Image.  From a boot state whose memory holds the file's bytes at `B`,
with the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after
writing to the UART the encoding of the array `printInt64 minValue`, followed by the status byte
0. -/
theorem int64min_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + int64minImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < int64minSize, b.core.mem (B + UInt64.ofNat j) = byteAt int64minBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B int64minLength)
        (fetchFrom b.core.mem B (codeWords int64minLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords int64minLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray (printInt64 Int64.minValue) ++
        [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h int64min_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Int64Text.printInt64_runs Int64.minValue (by decide) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- `printInt64 minValue`'s Image with the specification: the UART carries the encoding of
`expectedPrint Int64.minValue`, the words of the bytes of `-9223372036854775808`, and the status
0. -/
theorem int64min_image_spec (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + int64minImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < int64minSize, b.core.mem (B + UInt64.ofNat j) = byteAt int64minBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B int64minLength)
        (fetchFrom b.core.mem B (codeWords int64minLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords int64minLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray (expectedPrint Int64.minValue) ++
        [0] ∧
      expectedPrint Int64.minValue =
        Library.Numerics.Decimal.Shared.StrconvGrammar.words
          (Library.Numerics.Decimal.Shared.StrconvGrammar.ascii "-9223372036854775808") := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := int64min_image h B hB hlo hhi b hm hpc hoff
  exact ⟨b', r, hc, hx, hu, printInt64_eq Int64.minValue ▸ ho, by decide +kernel⟩

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.int64min_image
#print axioms TestSupport.A64.ImageFiles.int64min_image_spec
