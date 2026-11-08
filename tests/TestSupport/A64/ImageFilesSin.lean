import TestSupport.A64.Programs
import TestSupport.A64.Sin
import LeanExe.A64.File
import LeanExe.A64.Proof.ImageTheorem

/-!
The theorems of the sine's arm64 Images, `sin10.img` and `sin1e22.img`, which `a64-programs emit`
writes.  `tests/baremetal/a64-images.sh` elaborates this file in the directory of the Images, as it
does `tests/TestSupport/A64/ImageFiles.lean`, and no build target includes it.  The kernel evaluates
`genImage` on entry 15 of `Trig.compiled.module`, `Trig.sin`, and the word of 10 or of 10^22 at
`imageBase` and checks that the image's bytes are the file's.  `TestSupport.A64.Sin.runs` then joins
with `image_run_at`: for every base `B` that is a multiple of 4096 and whose image's memory lies in
the RAM GiB, from a boot state whose memory holds the file's bytes at `B`, with the program counter
there and the MMU off, the machine reaches `HVC #0` with X0 holding PSCI's `SYSTEM_OFF`, every store
to the UART complete, and the UART's output extended by the eight bytes of the word of `Trig.sin x`
and the status 0.  `sin10_accuracy` and `sin1e22_accuracy` add `TrigSinCos.sin_within`: the word
that the UART carries lies within one representable step of the nearest-even rounding of `sin 10` or
of `sin 10^22`.  The run on 10 reduces its argument by the multiples of `π/2` in `remMedium`, which
converts the rounded count, 6, to an integer with `FCVTZU`, and the run on 10^22 reduces it in
`remLarge`, which reads the bits of `2/π` and `π/2` from the tables that the module's initial store
borrows.
-/

namespace TestSupport.A64.ImageFiles

open LeanExe.A64 TestSupport.A64 Library.Numerics.Float64

def sin10Bytes : Nat := file_nat% "sin10.img"
def sin10Size : Nat := file_size% "sin10.img"

def sin10Length : Nat :=
  imageProgLength Trig.compiled.module 15 [0x4024000000000000] room cap .word imageBase

def sin10ImageSize : Nat :=
  imageSize Trig.compiled.module 15 [0x4024000000000000] room cap .word imageBase

def sin1e22Bytes : Nat := file_nat% "sin1e22.img"
def sin1e22Size : Nat := file_size% "sin1e22.img"

def sin1e22Length : Nat :=
  imageProgLength Trig.compiled.module 15 [0x4480F0CF064DD592] room cap .word imageBase

def sin1e22ImageSize : Nat :=
  imageSize Trig.compiled.module 15 [0x4480F0CF064DD592] room cap .word imageBase

set_option maxRecDepth 100000

theorem sin10_file : bytesOk (genImage Trig.compiled.module 15 [0x4024000000000000] room cap
    .word imageBase) sin10Bytes sin10Size = true := by decide +kernel

theorem sin1e22_file : bytesOk (genImage Trig.compiled.module 15 [0x4480F0CF064DD592] room cap
    .word imageBase) sin1e22Bytes sin1e22Size = true := by decide +kernel

theorem ten_bits : (Float.ofBits 0x4024000000000000).toBits = 0x4024000000000000 := by
  rw [LeanExe.ProofKit.F64Bits.toBits_ofBits]
  decide +kernel

theorem e22_bits : (Float.ofBits 0x4480F0CF064DD592).toBits = 0x4480F0CF064DD592 := by
  rw [LeanExe.ProofKit.F64Bits.toBits_ofBits]
  decide +kernel

/-- The sine's Image on 10.  From a boot state whose memory holds the file's bytes at `B`, with
the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after writing
to the UART the eight bytes of the word of `Trig.sin 10`, followed by the status byte 0. -/
theorem sin10 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + sin10ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < sin10Size, b.core.mem (B + UInt64.ofNat j) = byteAt sin10Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B sin10Length)
        (fetchFrom b.core.mem B (codeWords sin10Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords sin10Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (Trig.sin (Float.ofBits 0x4024000000000000)).toBits ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h sin10_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff (Sin.runs _ ten_bits room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- The sine's Image on 10 with the accuracy theorem: the UART carries the eight bytes of a word
`w` and the status 0, and `w` lies within one representable step of the nearest-even rounding of
`sin 10`. -/
theorem sin10_accuracy (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + sin10ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < sin10Size, b.core.mem (B + UInt64.ofNat j) = byteAt sin10Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B sin10Length)
        (fetchFrom b.core.mem B (codeWords sin10Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords sin10Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      LeanExe.ProofKit.F64SignedRounding.WithinSteps 1 (Real.sin 10) w := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := sin10 h B hB hlo hhi b hm hpc hoff
  have ha := Sin.within_one (Float.ofBits 0x4024000000000000) 10
    (by rw [ten_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel)
    (by rw [ten_bits]; exact_mod_cast Sin.value_of_scaled (q := 10) (by decide +kernel))
  exact ⟨b', _, r, hc, hx, hu, ho, ha⟩

/-- The sine's Image on 10^22.  From a boot state whose memory holds the file's bytes at `B`, with
the program counter there and the MMU off, the machine reaches PSCI's `SYSTEM_OFF` after writing
to the UART the eight bytes of the word of `Trig.sin 10^22`, followed by the status byte 0. -/
theorem sin1e22 (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + sin1e22ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < sin1e22Size, b.core.mem (B + UInt64.ofNat j) = byteAt sin1e22Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b', BootReach h (protectedBytes B sin1e22Length)
        (fetchFrom b.core.mem B (codeWords sin1e22Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords sin1e22Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++
        LeanExe.Native.encodeWord (Trig.sin (Float.ofBits 0x4480F0CF064DD592)).toBits ++ [0] := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := image_run_at h sin1e22_file (by decide) (by decide)
    (by decide) hB hlo hhi hm hpc hoff (Sin.runs _ e22_bits room cap)
  rcases ho with ho | ⟨_, hf, -⟩
  · exact ⟨b', r, hc, hx, hu, ho⟩
  · exact hf.elim

/-- The sine's Image on 10^22 with the accuracy theorem: the UART carries the eight bytes of a
word `w` and the status 0, and `w` lies within one representable step of the nearest-even rounding
of `sin 10^22`. -/
theorem sin1e22_accuracy (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + sin1e22ImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < sin1e22Size, b.core.mem (B + UInt64.ofNat j) = byteAt sin1e22Bytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ b' w, BootReach h (protectedBytes B sin1e22Length)
        (fetchFrom b.core.mem B (codeWords sin1e22Length)) b b' ∧
      fetchFrom b.core.mem B (codeWords sin1e22Length) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeWord w ++ [0] ∧
      LeanExe.ProofKit.F64SignedRounding.WithinSteps 1 (Real.sin (10 ^ 22)) w := by
  obtain ⟨b', r, hc, hx, hu, ho⟩ := sin1e22 h B hB hlo hhi b hm hpc hoff
  have ha := Sin.within_one (Float.ofBits 0x4480F0CF064DD592) ((10 : ℝ) ^ (22 : ℕ))
    (by rw [e22_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel)
    (by
      rw [e22_bits]
      exact_mod_cast Sin.value_of_scaled (q := (10 : ℤ) ^ (22 : ℕ)) (by decide +kernel))
  exact ⟨b', _, r, hc, hx, hu, ho, ha⟩

end TestSupport.A64.ImageFiles

#print axioms TestSupport.A64.ImageFiles.sin10
#print axioms TestSupport.A64.ImageFiles.sin10_accuracy
#print axioms TestSupport.A64.ImageFiles.sin1e22
#print axioms TestSupport.A64.ImageFiles.sin1e22_accuracy
