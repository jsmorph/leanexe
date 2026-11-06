import LeanExe.A64.Proof.ImageLayout
import LeanExe.A64.Proof.Lift
import LeanExe.A64.Proof.Table

/-!
The pieces that join the startup, the program, and the exit of an image in the boot model.  A
run of the program model stays a run under a code map that extends its own, so a program's
theorem, stated with the code map of the program's words, lifts to the code map of the whole
image.  The protected bytes of an image are those below the end of its translation table, and once
translation is on in the covered configuration with the image's table, the platform of the boot
model makes every other byte of the RAM GiB writable Normal memory and the UART writable Device
memory.
-/

namespace LeanExe.A64

theorem step_mono_code {P : Platform} {c1 c2 : UInt64 → Option UInt32} {s t : State}
    (hc : ∀ a w, c1 a = some w → c2 a = some w) (h : step P c1 s = some t) :
    step P c2 s = some t := by
  unfold step at h ⊢
  cases h1 : c1 s.pc with
  | none => rw [h1] at h; cases h
  | some w => rw [h1] at h; rw [hc _ _ h1]; exact h

/-- A run under a code map is a run under every code map that extends it. -/
theorem Reach.mono_code {P : Platform} {c1 c2 : UInt64 → Option UInt32} {s t : State}
    (hc : ∀ a w, c1 a = some w → c2 a = some w) (h : Reach P c1 s t) : Reach P c2 s t := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (step_mono_code hc hs) ih

/-- The bytes of the image at `image` that no store may change: those below the end of its
translation table, which follows the header, the startup, the program, and the vector table. -/
def protectedBytes (image : UInt64) (n : Nat) (a : UInt64) : Bool :=
  decide ((a - image).toNat < tabOff n + 32)

/-- The code map of an image's first `codeWords n` words maps only addresses in the RAM GiB, for
an image that lies in it. -/
theorem fetchFrom_ram {mem : UInt64 → UInt8} {image : UInt64} {N : Nat} {a : UInt64}
    {w : UInt32} (h : fetchFrom mem image N a = some w) (hlo : 0x40000000 ≤ image.toNat)
    (hhi : image.toNat + 4 * N ≤ 0x80000000) :
    0x40000000 ≤ a.toNat ∧ a.toNat < 0x80000000 ∧ (a - image).toNat < 4 * N := by
  unfold fetchFrom at h
  split at h
  · rename_i hin
    have h1 := hin.1
    rcases Nat.lt_or_ge a.toNat image.toNat with hl | hl
    · exfalso
      rw [UInt64.toNat_sub] at h1
      have := image.toNat_lt
      have := a.toNat_lt
      simp only [Nat.reducePow] at h1 this ⊢
      omega
    · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hl)] at h1
      exact ⟨by omega, by omega, hin.1⟩
  · cases h

/-- Under a boot state whose effective registers are the covered configuration with `tableBytes`
at `TTBR0_EL1`, the platform's Normal memory holds every byte of the RAM GiB that `R` leaves
unprotected. -/
theorem platform_normal {h : Hw} {R : UInt64 → Bool} {b : Boot}
    (hcov : b.eff.covered h = true)
    (htab : ∀ j (hj : j < 32), b.core.mem (b.eff.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    {a : UInt64} (hlo : 0x40000000 ≤ a) (hhi : a < 0x80000000) (hR : R a = false) :
    (b.platform h R).normal a = true := by
  simp only [Boot.platform, hR, Bool.not_false, Bool.true_and,
    classify_normal hcov htab hlo hhi, writableNormal]

end LeanExe.A64
