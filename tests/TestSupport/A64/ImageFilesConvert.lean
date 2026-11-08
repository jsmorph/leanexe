import TestSupport.A64.Programs
import TestSupport.A64.Convert
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the arm64 Images of `Examples.Convert`, `todouble.img`, `tosingle.img`,
`ofdouble.img`, and `convscale.img`, which `a64-programs emit` writes.
`tests/baremetal/a64-images.sh` elaborates this file in the directory of the Images, as it does
`tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.  The kernel evaluates
`genImage` on entry 2 of `Examples.Convert.compiled.module`, `toDouble`, at the word of
`-(2^53 + 3)`, on entry 3, `toSingle`, at the word of `-(2^62 + 2^38 + 1)`, on entry 4, `ofDouble`,
at the bits of the double below `-2^63`, and on entry 6, `scale`, at the word of -7 and the bits of
0.5, and checks that each image's bytes are the file's.  The programs' theorems of
`TestSupport.A64.Convert` then join with `image_run_at`: for every base `B` that is a multiple of
4096 and whose image's memory lies in the RAM GiB, from a boot state whose memory holds the file's
bytes at `B`, with the program counter there and the MMU off, the machine reaches `HVC #0` with X0
holding PSCI's `SYSTEM_OFF`, every store to the UART complete, and the UART's output extended by
the eight bytes of the result's word and the status 0.  Each theorem adds the specification of
`Examples.Convert.Spec`, WebAssembly's signed conversion as Talos defines it, and the value that the
kernel computes for it: `-(2^53 + 4)`, the tie rounded to the even significand; the single
`-(2^62 + 2^39)`, rounded once from the 64-bit magnitude; `minValue`, the saturation below `-2^63`;
and -3, the truncation of -3.5 toward zero.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64 Examples.Convert

def todoubleBytes : Nat := file_nat% "todouble.img"
def todoubleSize : Nat := file_size% "todouble.img"
def tosingleBytes : Nat := file_nat% "tosingle.img"
def tosingleSize : Nat := file_size% "tosingle.img"
def ofdoubleBytes : Nat := file_nat% "ofdouble.img"
def ofdoubleSize : Nat := file_size% "ofdouble.img"
def convscaleBytes : Nat := file_nat% "convscale.img"
def convscaleSize : Nat := file_size% "convscale.img"

/-- The word of `-(2^53 + 3)`. -/
abbrev wtie : UInt64 := 18437736874454810621
/-- The word of `-(2^62 + 2^38 + 1)`. -/
abbrev wsingle : UInt64 := 13835057780404256767
/-- The bits of the double below `-2^63`. -/
abbrev wbelow : UInt64 := 0xC3E0000000000001
/-- The word of -7. -/
abbrev wm7 : UInt64 := 18446744073709551609
/-- The bits of 0.5. -/
abbrev whalf : UInt64 := 0x3FE0000000000000

def todoubleLength : Nat := imageProgLength compiled.module 2 [wtie] room cap .word imageBase
def tosingleLength : Nat := imageProgLength compiled.module 3 [wsingle] room cap .word imageBase
def ofdoubleLength : Nat := imageProgLength compiled.module 4 [wbelow] room cap .word imageBase
def convscaleLength : Nat :=
  imageProgLength compiled.module 6 [wm7, whalf] room cap .word imageBase

def todoubleImageSize : Nat := imageSize compiled.module 2 [wtie] room cap .word imageBase
def tosingleImageSize : Nat := imageSize compiled.module 3 [wsingle] room cap .word imageBase
def ofdoubleImageSize : Nat := imageSize compiled.module 4 [wbelow] room cap .word imageBase
def convscaleImageSize : Nat := imageSize compiled.module 6 [wm7, whalf] room cap .word imageBase

set_option maxRecDepth 100000

theorem todouble_file : bytesOk (genImage compiled.module 2 [wtie] room cap .word imageBase)
    todoubleBytes todoubleSize = true := by decide +kernel

theorem tosingle_file : bytesOk (genImage compiled.module 3 [wsingle] room cap .word imageBase)
    tosingleBytes tosingleSize = true := by decide +kernel

theorem ofdouble_file : bytesOk (genImage compiled.module 4 [wbelow] room cap .word imageBase)
    ofdoubleBytes ofdoubleSize = true := by decide +kernel

theorem convscale_file : bytesOk (genImage compiled.module 6 [wm7, whalf] room cap .word
    imageBase) convscaleBytes convscaleSize = true := by decide +kernel

/-- `toDouble (-(2^53 + 3))`'s Image.  From a boot state whose memory holds the file's bytes at
`B`, with the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after
writing to the UART the eight bytes of a word `w` and the status byte 0, and `w` is
`f64.convert_i64_s` of the word of `-(2^53 + 3)`, the bits of `-(2^53 + 4)`. -/
theorem todouble_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + todoubleImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < todoubleSize, b.core.mem (B + UInt64.ofNat j) = byteAt todoubleBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B todoubleLength)
        (fetchFrom b.core.mem B (codeWords todoubleLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords todoubleLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w = expectedToDouble (-9007199254740995) ∧
        expectedToDouble (-9007199254740995) = 0xC340000000000002 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h todouble_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Convert.toDouble_runs (-9007199254740995) (by decide) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', _, r, hc, hx, hu, ho, toDouble_spec _, by decide +kernel⟩
  · exact hf.elim

/-- `toSingle (-(2^62 + 2^38 + 1))`'s Image: the UART carries the bits `w` of the single, zero
extended, and the status 0, and `w` is `f32.convert_i64_s` of the word of `-(2^62 + 2^38 + 1)`,
the bits of `-(2^62 + 2^39)`. -/
theorem tosingle_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + tosingleImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < tosingleSize, b.core.mem (B + UInt64.ofNat j) = byteAt tosingleBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B tosingleLength)
        (fetchFrom b.core.mem B (codeWords tosingleLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords tosingleLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w.toUInt64 ++ [0] ∧
      w = expectedToSingle (-4611686293305294849) ∧
        expectedToSingle (-4611686293305294849) = 0xDE800001 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h tosingle_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Convert.toSingle_runs (-4611686293305294849) (by decide) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', _, r, hc, hx, hu, ho, toSingle_spec _, by decide +kernel⟩
  · exact hf.elim

/-- `ofDouble` of the double below `-2^63`, `-(2^63 + 2^11)`, as an Image: the UART carries the
word `w` and the status 0, and `w` is `i64.trunc_sat_f64_s` of the double, the word of
`minValue`. -/
theorem ofdouble_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + ofdoubleImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < ofdoubleSize, b.core.mem (B + UInt64.ofNat j) = byteAt ofdoubleBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B ofdoubleLength)
        (fetchFrom b.core.mem B (codeWords ofdoubleLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords ofdoubleLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w = expectedOfDouble (Float.ofBits wbelow) ∧
        expectedOfDouble (Float.ofBits wbelow) = 0x8000000000000000 := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h ofdouble_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Convert.ofDouble_runs (Float.ofBits wbelow) (by decide +kernel) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', _, r, hc, hx, hu, ho, ofDouble_spec _, by decide +kernel⟩
  · exact hf.elim

/-- `scale (-7) 0.5`'s Image: the UART carries the word `w` and the status 0, and `w` is
`i64.trunc_sat_f64_s` of the product of `f64.convert_i64_s` of the word of -7 and 0.5, the word of
-3. -/
theorem convscale_image (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + convscaleImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < convscaleSize, b.core.mem (B + UInt64.ofNat j) = byteAt convscaleBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B convscaleLength)
        (fetchFrom b.core.mem B (codeWords convscaleLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords convscaleLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      w = expectedScale (-7) (Float.ofBits whalf) ∧
        expectedScale (-7) (Float.ofBits whalf) = 0xFFFFFFFFFFFFFFFD := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h convscale_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff
    (TestSupport.A64.Convert.scale_runs (-7) (Float.ofBits whalf) (by decide)
      (by decide +kernel) room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', _, r, hc, hx, hu, ho, scale_spec _ _, by decide +kernel⟩
  · exact hf.elim

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.todouble_image
#print axioms TestSupport.A64.ImageFiles.tosingle_image
#print axioms TestSupport.A64.ImageFiles.ofdouble_image
#print axioms TestSupport.A64.ImageFiles.convscale_image
