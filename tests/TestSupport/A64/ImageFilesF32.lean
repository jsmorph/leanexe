import TestSupport.A64.Programs
import TestSupport.A64.GptLayer32Runs
import TestSupport.A64.Conv32Runs
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the binary32 Images, `gptlayer32.img` and `conv32.img`, which `a64-programs emit`
writes.  `tests/baremetal/a64-images.sh` elaborates this file in the directory of the Images, as it
does `tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.  For each Image the
kernel evaluates `genImage` on the program's entry and argument at `imageBase` and checks that the
image's bytes are the file's, and the program's theorem `runs` joins with `image_run_at`: for every
base `B` that is a multiple of 4096 and whose image's memory lies in the RAM GiB, from a boot state
whose memory holds the file's bytes at `B`, with the program counter there and the MMU off, the
machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store to the UART complete,
and the UART's output extended by the encoding of the program's array, its length word and its
elements, and the status 0.  The programs run single-precision instructions, whose meanings in the
model are Talos's IEEE 754 functions of binary32.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64

def gptlayer32Bytes : Nat := file_nat% "gptlayer32.img"
def gptlayer32Size : Nat := file_size% "gptlayer32.img"

def gptlayer32Length : Nat :=
  imageProgLength TestSupport.A64.Gpt32.compiled.module 14 [2] room cap .array imageBase

def gptlayer32ImageSize : Nat :=
  imageSize TestSupport.A64.Gpt32.compiled.module 14 [2] room cap .array imageBase

def conv32Bytes : Nat := file_nat% "conv32.img"
def conv32Size : Nat := file_size% "conv32.img"

def conv32Length : Nat :=
  imageProgLength TestSupport.A64.Conv32.compiled.module 4 [64] room cap .array imageBase

def conv32ImageSize : Nat :=
  imageSize TestSupport.A64.Conv32.compiled.module 4 [64] room cap .array imageBase

set_option maxRecDepth 100000

theorem gptlayer32_file : bytesOk (genImage TestSupport.A64.Gpt32.compiled.module 14 [2] room cap
    .array imageBase) gptlayer32Bytes gptlayer32Size = true := by decide +kernel

/-- The binary32 GPT-2 layer's Image.  From a boot state whose memory holds the file's bytes at
`B`, with the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after
writing to the UART the encoding of the words of the row that `Demos.Gpt32.layerStep32` gives at
position 2 for one head and an MLP of width 64, with the weights `Gpt32.layer`, the row
`Gpt32.row0`, and the caches `Gpt32.keys0 2` and `Gpt32.values0 2`, followed by the status
byte 0. -/
theorem gptlayer32 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + gptlayer32ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < gptlayer32Size, b.core.mem (B + UInt64.ofNat j) = byteAt gptlayer32Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B gptlayer32Length)
        (fetchFrom b.core.mem B (codeWords gptlayer32Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords gptlayer32Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray
        ((Demos.Gpt32.layerStep32 1 64 2 Gpt32.layer Gpt32.row0 (Gpt32.keys0 2)
          (Gpt32.values0 2)).1.map fun x => x.toBits.toUInt64) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h gptlayer32_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff (Gpt32.runs room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, Gpt32.layerCheck_eq 2 ▸ ho⟩
  · exact hf.elim

theorem conv32_file : bytesOk (genImage TestSupport.A64.Conv32.compiled.module 4 [64] room cap
    .array imageBase) conv32Bytes conv32Size = true := by decide +kernel

/-- The binary32 conversions' Image.  From a boot state whose memory holds the file's bytes at
`B`, with the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after
writing to the UART the encoding of `Conv32.convCheck 64`, the four words of `Conv32.convWord` of
each input below 64, followed by the status byte 0. -/
theorem conv32 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + conv32ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < conv32Size, b.core.mem (B + UInt64.ofNat j) = byteAt conv32Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B conv32Length)
        (fetchFrom b.core.mem B (codeWords conv32Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords conv32Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray (Conv32.convCheck 64) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h conv32_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff (Conv32.runs room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.gptlayer32
#print axioms TestSupport.A64.ImageFiles.conv32
