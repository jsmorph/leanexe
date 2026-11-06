import TestSupport.A64.Programs
import TestSupport.A64.Gcd
import TestSupport.A64.Crc
import TestSupport.A64.Sha
import TestSupport.A64.Fold
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the arm64 Images that `a64-programs emit` writes.
`tests/baremetal/a64-images.sh` elaborates this file in the directory of those files after it emits
them, so `file_nat%` and `file_size%` read each NAME.img, and no build target includes it.  For each
program the kernel evaluates `genImage` on the program's module, entry, arguments, stack, cap, and
form of result at `imageBase`, and checks that the image's bytes are the file's.  The program's
theorem then joins with `image_run`: from a boot state whose memory holds the file's bytes at
`imageBase`, with the program counter there and the MMU off, the machine reaches `HVC #0` with
X0 holding PSCI's `SYSTEM_OFF`, every store to the UART complete, and the UART's output extended
by the result's bytes and the status 0, or, where the program's theorem allows a trap, by the
status byte alone: 4 for an overflow of the stack in GCD's recursion, and 1 or 4 in Fold's.
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

theorem gcd (h : Hw) (b : Boot)
    (hm : ∀ j < gcdSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt gcdBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes imageBase gcdLength)
        (fetchFrom b.core.mem imageBase (codeWords gcdLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords gcdLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run (T := fun _ => False) h gcd_file (by decide)
    (by decide) (by decide) hm hpc hoff (by
      intro P area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
      obtain ⟨ms', hr, hp, -, hx, ho⟩ := TestSupport.A64.Gcd.program P _ room area cap hg ms
        himage hpc hal hroom htop hstack h17 harea hamap habove
      exact .inl ⟨ms', hr, hp, hx, ho⟩)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem gcdrec (h : Hw) (b : Boot)
    (hm : ∀ j < gcdrecSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt gcdrecBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes imageBase gcdrecLength)
        (fetchFrom b.core.mem imageBase (codeWords gcdrecLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords gcdrecLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++
          LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) ++ [0] ∨
        b'.core.out = b.core.out ++ [4]) := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run (T := fun c => c = 4) h gcdrec_file (by decide)
    (by decide) (by decide) hm hpc hoff (by
      intro P area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
      exact (TestSupport.A64.Gcd.rec_program P _ room area cap hg ms himage hpc hal hroom htop
        hstack h17 harea hamap habove).imp (fun ⟨ms', hr, hp, _, hx, ho⟩ => ⟨ms', hr, hp, hx, ho⟩)
        id)
  refine ⟨b', r, hc, hx, hu, ho.imp id ?_⟩
  rintro ⟨c, rfl, h⟩
  exact h

theorem crc32 (h : Hw) (b : Boot)
    (hm : ∀ j < crcSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt crcBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes imageBase crcLength)
        (fetchFrom b.core.mem imageBase (codeWords crcLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords crcLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (TestSupport.Bare.crcCheck 0x3837363534333231 0x39) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run (T := fun _ => False) h crc32_file (by decide)
    (by decide) (by decide) hm hpc hoff (by
      intro P area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
      obtain ⟨ms', hr, hp, -, hx, ho⟩ := TestSupport.A64.Crc.program P _ room area cap hg ms
        himage hpc hal hroom htop hstack h17 harea hamap habove
      exact .inl ⟨ms', hr, hp, hx, ho⟩)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem sha256 (h : Hw) (b : Boot)
    (hm : ∀ j < shaSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt shaBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes imageBase shaLength)
        (fetchFrom b.core.mem imageBase (codeWords shaLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords shaLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeArray (TestSupport.Bare.shaCheck 0x636261) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run (T := fun _ => False) h sha256_file (by decide)
    (by decide) (by decide) hm hpc hoff (by
      intro P area _ hg ms himage hpc hal _ htop hstack h17 harea hamap habove
      obtain ⟨ms', hr, hp, -, hx, ho⟩ := TestSupport.A64.Sha.program P _ room area cap hg ms
        himage hpc hal (by decide) htop hstack h17 harea hamap habove
      exact .inl ⟨ms', hr, hp, hx, ho⟩)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

theorem depth (h : Hw) (b : Boot)
    (hm : ∀ j < depthSize, b.core.mem (imageBase + UInt64.ofNat j) = byteAt depthBytes j)
    (hpc : b.core.pc = imageBase) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes imageBase depthLength)
        (fetchFrom b.core.mem imageBase (codeWords depthLength)) b b' ∧
      fetchFrom b.core.mem imageBase (codeWords depthLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++
          LeanExe.Native.encodeWord (Verified.Examples.Fold.recursive 1000) ++ [0] ∨
        b'.core.out = b.core.out ++ [1] ∨ b'.core.out = b.core.out ++ [4]) := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run (T := fun c => c = 1 ∨ c = 4) h depth_file
    (by decide) (by decide) (by decide) hm hpc hoff (by
      intro P area _ hg ms himage hpc hal hroom htop hstack h17 harea hamap habove
      exact (TestSupport.A64.Fold.program P _ room area cap hg ms himage hpc hal hroom htop hstack
        h17 harea hamap habove).imp (fun ⟨ms', hr, hp, _, hx, ho⟩ => ⟨ms', hr, hp, hx, ho⟩) id)
  refine ⟨b', r, hc, hx, hu, ho.imp id ?_⟩
  rintro ⟨c, rfl | rfl, h⟩
  · exact .inl h
  · exact .inr h

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.gcd
#print axioms TestSupport.A64.ImageFiles.gcdrec
#print axioms TestSupport.A64.ImageFiles.crc32
#print axioms TestSupport.A64.ImageFiles.sha256
#print axioms TestSupport.A64.ImageFiles.depth
