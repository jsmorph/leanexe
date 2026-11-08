import TestSupport.A64.Programs
import TestSupport.A64.Gcd
import TestSupport.A64.Crc
import TestSupport.A64.Sha
import TestSupport.A64.Fold
import TestSupport.A64.Cic
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the arm64 Images that `a64-programs emit` writes.
`tests/baremetal/a64-images.sh` elaborates this file in the directory of those files after it emits
them, so `file_nat%` and `file_size%` read each NAME.img, and no build target includes it.  For each
program the kernel evaluates `genImage` on the program's module, entry, arguments, stack, cap, and
form of result at `imageBase`, and checks that the image's bytes are the file's.  The program's
theorem, in the form `ProgramRuns` at the image's room and cap, then joins with `image_run_at`: for
every base `B` that is a multiple of 4096 and whose image's memory lies in the RAM GiB, from a boot
state whose memory holds the file's bytes at `B`, with the program counter there and the MMU off,
the machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store to the UART complete,
and the UART's output extended by the result's bytes and the status 0, or, where the program's
theorem allows a trap, by the status byte alone: 4 for an overflow of the stack in GCD's
recursion, and 1 or 4 in Fold's.  `cic_outputs` states the CIC filter's run with the specification
over ℤ: the array that the UART receives has as its elements, read as signed 64-bit integers, the
outputs `Library.Numerics.Filters.Cic.outputs 3 8 1` of the table's samples read as integers.  The
Euler solver's Image has its theorem in `tests/TestSupport/A64/ImageFilesEuler.lean`, which the
script elaborates on its own: the kernel's check of that Image takes about 12 GB, and the checks of
this file about 6 GB.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64

def gcdBytes : Nat := file_nat% "gcd.img"
def gcdSize : Nat := file_size% "gcd.img"
def gcdrecBytes : Nat := file_nat% "gcdrec.img"
def gcdrecSize : Nat := file_size% "gcdrec.img"
def crcBytes : Nat := file_nat% "crc32.img"
def crcSize : Nat := file_size% "crc32.img"
def shaBytes : Nat := file_nat% "sha256.img"
def shaSize : Nat := file_size% "sha256.img"
def depthBytes : Nat := file_nat% "depth.img"
def depthSize : Nat := file_size% "depth.img"
def cicBytes : Nat := file_nat% "cic.img"
def cicSize : Nat := file_size% "cic.img"

def gcdLength : Nat :=
  imageProgLength TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] room cap .word imageBase
def gcdrecLength : Nat :=
  imageProgLength TestSupport.Native.Gcd.recCompiled.module 3 [1071, 462] room cap .word imageBase
def crcLength : Nat := imageProgLength TestSupport.Bare.crcCompiled.module 5
  [0x3837363534333231, 0x39] room cap .word imageBase
def shaLength : Nat :=
  imageProgLength TestSupport.Bare.shaCompiled.module 11 [0x636261] room cap .array imageBase
def depthLength : Nat :=
  imageProgLength Verified.Examples.Fold.compiled.module 13 [1000] room cap .word imageBase
def cicLength : Nat :=
  imageProgLength TestSupport.A64.Cic.compiled.module 7 [64] room cap .array imageBase

def gcdImageSize : Nat :=
  imageSize TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] room cap .word imageBase
def gcdrecImageSize : Nat :=
  imageSize TestSupport.Native.Gcd.recCompiled.module 3 [1071, 462] room cap .word imageBase
def crcImageSize : Nat := imageSize TestSupport.Bare.crcCompiled.module 5
  [0x3837363534333231, 0x39] room cap .word imageBase
def shaImageSize : Nat :=
  imageSize TestSupport.Bare.shaCompiled.module 11 [0x636261] room cap .array imageBase
def depthImageSize : Nat :=
  imageSize Verified.Examples.Fold.compiled.module 13 [1000] room cap .word imageBase
def cicImageSize : Nat :=
  imageSize TestSupport.A64.Cic.compiled.module 7 [64] room cap .array imageBase

set_option maxRecDepth 100000

theorem gcd_file : bytesOk (genImage TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] room
    cap .word imageBase) gcdBytes gcdSize = true := by decide +kernel

theorem gcdrec_file : bytesOk (genImage TestSupport.Native.Gcd.recCompiled.module 3 [1071, 462]
    room cap .word imageBase) gcdrecBytes gcdrecSize = true := by decide +kernel

theorem crc32_file : bytesOk (genImage TestSupport.Bare.crcCompiled.module 5
    [0x3837363534333231, 0x39] room cap .word imageBase) crcBytes crcSize = true := by
  decide +kernel

theorem sha256_file : bytesOk (genImage TestSupport.Bare.shaCompiled.module 11 [0x636261] room cap
    .array imageBase) shaBytes shaSize = true := by decide +kernel

theorem depth_file : bytesOk (genImage Verified.Examples.Fold.compiled.module 13 [1000] room cap
    .word imageBase) depthBytes depthSize = true := by decide +kernel

theorem cic_file : bytesOk (genImage TestSupport.A64.Cic.compiled.module 7 [64] room cap .array
    imageBase) cicBytes cicSize = true := by decide +kernel

theorem gcd (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + gcdImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < gcdSize, b.core.mem (B + UInt64.ofNat j) = byteAt gcdBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B gcdLength) (fetchFrom b.core.mem B (codeWords gcdLength))
        b b' ∧
      fetchFrom b.core.mem B (codeWords gcdLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h gcd_file (by decide) (by decide) (by decide) hB
    hlo hhi hm hpc hoff (Gcd.runs room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem gcdrec (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + gcdrecImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < gcdrecSize, b.core.mem (B + UInt64.ofNat j) = byteAt gcdrecBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B gcdrecLength)
        (fetchFrom b.core.mem B (codeWords gcdrecLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords gcdrecLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++
          LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) ++ [0] ∨
        b'.core.out = b.core.out ++ [4]) := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h gcdrec_file (by decide) (by decide) (by decide)
    hB hlo hhi hm hpc hoff (Gcd.rec_runs room cap)
  refine ⟨b', r, hc, hx, hu, ho.imp id ?_⟩
  rintro ⟨c, rfl, h⟩
  exact h

theorem crc32 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + crcImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < crcSize, b.core.mem (B + UInt64.ofNat j) = byteAt crcBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B crcLength) (fetchFrom b.core.mem B (codeWords crcLength))
        b b' ∧
      fetchFrom b.core.mem B (codeWords crcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h crc32_file (by decide) (by decide) (by decide) hB
    hlo hhi hm hpc hoff (Crc.runs room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem sha256 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + shaImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < shaSize, b.core.mem (B + UInt64.ofNat j) = byteAt shaBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B shaLength) (fetchFrom b.core.mem B (codeWords shaLength))
        b b' ∧
      fetchFrom b.core.mem B (codeWords shaLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeArray (TestSupport.Bare.shaCheck 0x636261) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h sha256_file (by decide) (by decide) (by decide)
    hB hlo hhi hm hpc hoff (Sha.runs room cap (by decide))
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem depth (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + depthImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < depthSize, b.core.mem (B + UInt64.ofNat j) = byteAt depthBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B depthLength)
        (fetchFrom b.core.mem B (codeWords depthLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords depthLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++
          LeanExe.Native.encodeWord (Verified.Examples.Fold.recursive 1000) ++ [0] ∨
        b'.core.out = b.core.out ++ [1] ∨ b'.core.out = b.core.out ++ [4]) := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h depth_file (by decide) (by decide) (by decide)
    hB hlo hhi hm hpc hoff (Fold.runs room cap)
  refine ⟨b', r, hc, hx, hu, ho.imp id ?_⟩
  rintro ⟨c, rfl | rfl, h⟩
  · exact .inl h
  · exact .inr h

theorem cic (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + cicImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < cicSize, b.core.mem (B + UInt64.ofNat j) = byteAt cicBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B cicLength) (fetchFrom b.core.mem B (codeWords cicLength))
        b b' ∧
      fetchFrom b.core.mem B (codeWords cicLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray (TestSupport.A64.Cic.cicCheck 64) ++
        [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h cic_file (by decide) (by decide) (by decide) hB
    hlo hhi hm hpc hoff (Cic.runs room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- The CIC filter's Image computes the filter of the specification over ℤ.  From a boot state whose
memory holds the file's bytes at `B`, with the program counter there and the MMU off, the machine
reaches PSCI's `SYSTEM_OFF` after writing to the UART the encoding of an array of words, its length
word and its elements, followed by the status byte 0.  The array's elements, read as signed 64-bit
integers, are the outputs of the CIC decimation filter of order 3, decimation 8, and differential
delay 1, as `outputs` of `Library/Numerics/Filters/Cic/Spec.lean` defines them over ℤ, on the
table's samples read as integers. -/
theorem cic_outputs (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + cicImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < cicSize, b.core.mem (B + UInt64.ofNat j) = byteAt cicBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ (b' : Boot) (ys : Array UInt64), BootReach h (protectedBytes B cicLength)
        (fetchFrom b.core.mem B (codeWords cicLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords cicLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray ys ++ [0] ∧
      ys.toList.map (fun w => w.toBitVec.toInt) =
        Library.Numerics.Filters.Cic.outputs 3 8 1
          (TestSupport.A64.Cic.input.toList.map fun w => w.toBitVec.toInt) := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := cic h B hB hlo hhi b hm hpc hoff
  exact ⟨b', _, r, hc, hx, hu, ho, Cic.check_toInt⟩

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.gcd
#print axioms TestSupport.A64.ImageFiles.gcdrec
#print axioms TestSupport.A64.ImageFiles.crc32
#print axioms TestSupport.A64.ImageFiles.sha256
#print axioms TestSupport.A64.ImageFiles.depth
#print axioms TestSupport.A64.ImageFiles.cic
#print axioms TestSupport.A64.ImageFiles.cic_outputs
