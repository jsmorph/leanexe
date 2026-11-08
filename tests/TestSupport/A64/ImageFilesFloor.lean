import TestSupport.A64.Programs
import TestSupport.A64.Floor
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the arm64 Images of `Examples.Floor`, `floordiv.img`, `floordivmin.img`, and
`average.img`, which `a64-programs emit` writes.  `tests/baremetal/a64-images.sh` elaborates this
file in the directory of the Images, as it does `tests/TestSupport/A64/ImageFiles.lean`, and no
build target includes it.  The kernel evaluates `genImage` on entry 2 of
`Examples.Floor.compiled.module`, `floorDiv`, at the words of -7 and 2 and of `minValue` and -1, and
on entry 3, `average`, at the words of `minValue` and -1, and checks that each image's bytes are
the file's.  `TestSupport.A64.Floor.floorDiv_runs` and `average_runs` then join with
`image_run_at`: for every base `B` that is a multiple of 4096 and whose image's memory lies in the
RAM GiB, from a boot state whose memory holds the file's bytes at `B`, with the program counter
there and the MMU off, the machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every
store to the UART complete, and the UART's output extended by the eight bytes of the result's word
and the status 0.  `floordiv_image_spec` and `average_image_spec` add the specifications: the word
that the UART carries is that of the `Int64` whose integer is `Int.fdiv (-7) 2 = -4` or
`Int.fdiv (-2^63 - 1) 2 = -2^62 - 1`.  `floordivmin_image` states the wrapped quotient: `floorDiv`
gives `minValue` for `minValue` by -1, outside the specification's domain.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64 Examples.Floor

def floordivBytes : Nat := file_nat% "floordiv.img"
def floordivSize : Nat := file_size% "floordiv.img"
def floordivminBytes : Nat := file_nat% "floordivmin.img"
def floordivminSize : Nat := file_size% "floordivmin.img"
def averageBytes : Nat := file_nat% "average.img"
def averageSize : Nat := file_size% "average.img"

/-- The word of -7. -/
abbrev wm7 : UInt64 := 18446744073709551609
/-- The word of `minValue`. -/
abbrev wmin : UInt64 := 9223372036854775808
/-- The word of -1. -/
abbrev wm1 : UInt64 := 18446744073709551615

def floordivLength : Nat := imageProgLength compiled.module 2 [wm7, 2] room cap .word imageBase
def floordivminLength : Nat :=
  imageProgLength compiled.module 2 [wmin, wm1] room cap .word imageBase
def averageLength : Nat := imageProgLength compiled.module 3 [wmin, wm1] room cap .word imageBase

def floordivImageSize : Nat := imageSize compiled.module 2 [wm7, 2] room cap .word imageBase
def floordivminImageSize : Nat :=
  imageSize compiled.module 2 [wmin, wm1] room cap .word imageBase
def averageImageSize : Nat := imageSize compiled.module 3 [wmin, wm1] room cap .word imageBase

set_option maxRecDepth 100000

theorem floordiv_file : bytesOk (genImage compiled.module 2 [wm7, 2] room cap .word imageBase)
    floordivBytes floordivSize = true := by decide +kernel

theorem floordivmin_file : bytesOk (genImage compiled.module 2 [wmin, wm1] room cap .word
    imageBase) floordivminBytes floordivminSize = true := by decide +kernel

theorem average_file : bytesOk (genImage compiled.module 3 [wmin, wm1] room cap .word imageBase)
    averageBytes averageSize = true := by decide +kernel

/-- `floorDiv (-7) 2`'s Image.  From a boot state whose memory holds the file's bytes at `B`, with
the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after writing to
the UART the eight bytes of the word of `floorDiv (-7) 2`, followed by the status byte 0. -/
theorem floordiv_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + floordivImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < floordivSize, b.core.mem (B + UInt64.ofNat j) = byteAt floordivBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B floordivLength)
        (fetchFrom b.core.mem B (codeWords floordivLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords floordivLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord (floorDiv (-7) 2).toUInt64 ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h floordiv_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Floor.floorDiv_runs (-7) 2 (by decide) (by decide) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- `floorDiv minValue (-1)`'s Image, whose result is the wrapped quotient `minValue`. -/
theorem floordivmin_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + floordivminImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < floordivminSize, b.core.mem (B + UInt64.ofNat j) = byteAt floordivminBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B floordivminLength)
        (fetchFrom b.core.mem B (codeWords floordivminLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords floordivminLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord wmin ++ [0] := by
  have hv : (floorDiv Int64.minValue (-1)).toUInt64 = wmin := by decide
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h floordivmin_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Floor.floorDiv_runs Int64.minValue (-1) (by decide) (by decide) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, hv ▸ ho⟩
  · exact hf.elim

/-- `average minValue (-1)`'s Image. -/
theorem average_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + averageImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < averageSize, b.core.mem (B + UInt64.ofNat j) = byteAt averageBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B averageLength)
        (fetchFrom b.core.mem B (codeWords averageLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords averageLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (Examples.Floor.average Int64.minValue (-1)).toUInt64 ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h average_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Floor.average_runs Int64.minValue (-1) (by decide) (by decide) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- `floorDiv (-7) 2`'s Image with the specification: the UART carries the eight bytes of a word
`w` and the status 0, and `w` is the word of the `Int64` whose integer is `Int.fdiv (-7) 2`, which
is -4. -/
theorem floordiv_image_spec (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + floordivImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < floordivSize, b.core.mem (B + UInt64.ofNat j) = byteAt floordivBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B floordivLength)
        (fetchFrom b.core.mem B (codeWords floordivLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords floordivLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w.toInt64.toInt = expectedDiv (-7) 2 ∧ expectedDiv (-7) 2 = -4 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := floordiv_image h B hB hlo hhi b hm hpc hoff
  have hs := floorDiv_spec (-7) 2 (by decide) (by decide)
  exact ⟨b', _, r, hc, hx, hu, ho, hs, by decide⟩

/-- `average minValue (-1)`'s Image with the specification: the UART carries the eight bytes of a
word `w` and the status 0, and `w` is the word of the `Int64` whose integer is the floor of the
mean of `-2^63` and -1, which is `-2^62 - 1`. -/
theorem average_image_spec (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + averageImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < averageSize, b.core.mem (B + UInt64.ofNat j) = byteAt averageBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B averageLength)
        (fetchFrom b.core.mem B (codeWords averageLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords averageLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w.toInt64.toInt = expectedAverage Int64.minValue (-1) ∧
        expectedAverage Int64.minValue (-1) = -2 ^ 62 - 1 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := average_image h B hB hlo hhi b hm hpc hoff
  have hs := Examples.Floor.average_spec Int64.minValue (-1)
  exact ⟨b', _, r, hc, hx, hu, ho, hs, by decide⟩

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.floordiv_image
#print axioms TestSupport.A64.ImageFiles.floordivmin_image
#print axioms TestSupport.A64.ImageFiles.average_image
#print axioms TestSupport.A64.ImageFiles.floordiv_image_spec
#print axioms TestSupport.A64.ImageFiles.average_image_spec
