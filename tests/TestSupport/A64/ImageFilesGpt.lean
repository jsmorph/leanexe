import TestSupport.A64.Programs
import TestSupport.A64.Gpt
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorem of the GPT-2 kernel's arm64 Image, `gptscores.img`, which `a64-programs emit` writes.
`tests/baremetal/a64-images.sh` elaborates this file in the directory of the Images, as it does
`tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.  The kernel evaluates
`genImage` on entry 14 of `TestSupport.A64.Gpt.compiled.module` and the argument 3 at `imageBase`
and checks that the image's bytes are the file's.  `TestSupport.A64.Gpt.runs` then joins with
`image_run_at`, and `TestSupport.A64.Gpt.scoresCheck_eq` states the result with `Demos.Gpt.scores`:
for every base `B` that is a multiple of 4096 and whose image's memory lies in the RAM GiB, from a
boot state whose memory holds the file's bytes at `B`, with the program counter there and the MMU
off, the machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store to the UART
complete, and the UART's output extended by the encoding of the words of the scores, its length
word and its elements, and the status 0.  The program runs floating-point instructions, whose
meanings in the model are Talos's IEEE 754 functions.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64

def gptscoresBytes : Nat := file_nat% "gptscores.img"
def gptscoresSize : Nat := file_size% "gptscores.img"

def gptscoresLength : Nat :=
  imageProgLength TestSupport.A64.Gpt.compiled.module 14 [3] room cap .array imageBase

def gptscoresImageSize : Nat :=
  imageSize TestSupport.A64.Gpt.compiled.module 14 [3] room cap .array imageBase

set_option maxRecDepth 100000

theorem gptscores_file : bytesOk (genImage TestSupport.A64.Gpt.compiled.module 14 [3] room cap
    .array imageBase) gptscoresBytes gptscoresSize = true := by decide +kernel

/-- The GPT-2 kernel's Image.  From a boot state whose memory holds the file's bytes at `B`, with
the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after writing to
the UART the encoding of the words of `Demos.Gpt.scores` on the cache of 3 positions, the 32
embeddings, and the final layer norm's gains and biases, with one layer, two heads of width 8, and
`eps` 1e-5, followed by the status byte 0. -/
theorem gptscores (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + gptscoresImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < gptscoresSize, b.core.mem (B + UInt64.ofNat j) = byteAt gptscoresBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B gptscoresLength)
        (fetchFrom b.core.mem B (codeWords gptscoresLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords gptscoresLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray
        ((Demos.Gpt.scores (Gpt.cacheOf 3) (Gpt.embeddings 32 16) (Gpt.gains 16) (Gpt.biases 16)
          1 2 8 32 1e-5).map Float.toBits) ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h gptscores_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff (Gpt.runs room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, Gpt.scoresCheck_eq 3 ▸ ho⟩
  · exact hf.elim

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.gptscores
