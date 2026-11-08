import LeanExe.A64.Proof.ImageLayout
import LeanExe.A64.Proof.Lift
import LeanExe.A64.Proof.Table
import LeanExe.A64.Proof.Exit

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

theorem image_add_64 (a : UInt64) : a + 64 = after a 16 := by
  simp [after]

theorem layout_base (image : UInt64) (n : Nat) (m : Wasm.Module) (cap : Nat) (room : UInt64) :
    (layoutOf image n m cap room).base = after (image + 64) 70 := by
  show image + UInt64.ofNat (64 + 4 * startupLength) = image + 64 + 4 * UInt64.ofNat startupLength
  rw [UInt64.add_assoc]
  rfl

/-- A boot state ready for the program: SP_EL1 selected, the written system registers in effect
in the covered configuration with clean TLBs, the translation table in memory at `TTBR0_EL1` and
protected by `R`, and every address of the code map executable Normal memory. -/
structure Ready (h : Hw) (R : UInt64 → Bool) (code : UInt64 → Option UInt32) (b : Boot) :
    Prop where
  sp : b.spSel = true
  sync : b.written = b.eff
  cov : b.eff.covered h = true
  tlb : b.tlb = .clean
  tab : ∀ j (hj : j < 32), b.core.mem (b.eff.ttbr0 + UInt64.ofNat j) = tableBytes[j]
  prot : ∀ j < 32, R (b.eff.ttbr0 + UInt64.ofNat j) = true
  exe : ∀ a w, code a = some w → ∃ x, classify h b.eff b.core.mem a = some (.normal x true)

/-- A run of the program model under a ready state's platform keeps the state ready. -/
theorem Ready.reach {h : Hw} {R : UInt64 → Bool} {code c' : UInt64 → Option UInt32} {b : Boot}
    (hr : Ready h R code b) {c : State} (hrun : Reach (b.platform h R) c' b.core c) (u : Bool) :
    Ready h R code { b with core := c, uartDone := u } := by
  have hkeep : ∀ j < 32, c.mem (b.eff.ttbr0 + UInt64.ofNat j) =
      b.core.mem (b.eff.ttbr0 + UInt64.ofNat j) := fun j hj =>
    Reach.frame hrun (by simp [Boot.platform, hr.prot j hj])
  refine ⟨hr.sp, hr.sync, hr.cov, hr.tlb, fun j hj => ?_, hr.prot, fun a w hw => ?_⟩
  · show c.mem _ = _
    rw [hkeep j hj]
    exact hr.tab j hj
  · show ∃ x, classify h b.eff c.mem a = _
    rw [classify_congr hkeep]
    exact hr.exe a w hw

/-- The rest of an image's run once the program starts: when the program, in the program model
with a code map that the image's extends, either returns to the exit with X0 = 0 after writing
`out`, or reaches the exit word with a status that satisfies `T` and writes nothing, the boot
model reaches the `HVC #0` with X0 holding `SYSTEM_OFF`, every UART store complete, and the UART
showing `out` followed by the byte 0, or the status's byte alone. -/
theorem boot_after_main {L : Layout} {is : List Instr} (hs : startupCode L = .ok is)
    {code pcode : UInt64 → Option UInt32} (hc : CodeAt code (L.image + 64) is)
    (hbase : L.base = after (L.image + 64) 70) (hmono : ∀ a w, pcode a = some w → code a = some w)
    {h : Hw} {R : UInt64 → Bool} {b : Boot} (hr : Ready h R code b) {out : List UInt8}
    {T : UInt64 → Prop}
    (hout : (∃ ms', Reach (b.platform h R) pcode b.core ms' ∧
        ms'.pc = after (L.image + 64) 58 ∧ ms'.x 0 = 0 ∧ ms'.out = b.core.out ++ out) ∨
      ∃ ms', Reach (b.platform h R) pcode b.core ms' ∧ ms'.pc = L.base ∧ T (ms'.x 0) ∧
        ms'.out = b.core.out) :
    ∃ b', BootReach h R code b b' ∧ code b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      (b'.core.out = b.core.out ++ out ++ [0] ∨
        ∃ c, T c ∧ b'.core.out = b.core.out ++ [c.toUInt8]) := by
  have hu := classify_uart hr.cov hr.tab
  rcases hout with ⟨ms, hrun, hp, hx, ho⟩ | ⟨ms, hrun, hp, ht, ho⟩
  · have hrun' := Reach.mono_code hmono hrun
    have r1 := bootReach_of_reach hr.sp hr.sync hr.cov hr.tlb hu hr.prot hr.exe hrun'
    have hr1 := hr.reach hrun' (b.uartDone && ms.out == b.core.out)
    obtain ⟨b', r2, -, hcb, hx', ho', hu'⟩ := boot_exit hs hc hr1.sp hr1.sync hr1.cov hr1.tlb
      hr1.tab hr1.prot hr1.exe hp
    refine ⟨b', r1.trans r2, hcb, hx', hu', .inl ?_⟩
    rw [ho']
    show ms.out ++ [(ms.x 0).toUInt8] = _
    rw [ho, hx]
    rfl
  · have hrun' := Reach.mono_code hmono hrun
    have hw := run_exitWord (P := b.platform h R) hs hc hbase hp
    have hboth := hrun'.trans hw
    have r1 := bootReach_of_reach hr.sp hr.sync hr.cov hr.tlb hu hr.prot hr.exe hboth
    have hr1 := hr.reach hboth (b.uartDone && ms.out == b.core.out)
    obtain ⟨b', r2, -, hcb, hx', ho', hu'⟩ := boot_exit hs hc hr1.sp hr1.sync hr1.cov hr1.tlb
      hr1.tab hr1.prot hr1.exe rfl
    refine ⟨b', r1.trans r2, hcb, hx', hu', .inr ⟨ms.x 0, ht, ?_⟩⟩
    rw [ho']
    show ms.out ++ [(ms.x 0).toUInt8] = _
    rw [ho]

/-- A code map of `n` words from `a'`, word `o` of a code map of `N` words from `a`, whose memory
agrees with the larger map's memory on its bytes, is part of the larger map. -/
theorem fetchFrom_sub {m m' : UInt64 → UInt8} {a a' : UInt64} {o n N : Nat}
    (ha' : a' = a + UInt64.ofNat (4 * o)) (hon : o + n ≤ N) (hN : 4 * N < 2 ^ 64)
    (hm : ∀ j < 4 * n, m' (a' + UInt64.ofNat j) = m (a' + UInt64.ofNat j))
    {p : UInt64} {w : UInt32} (h : fetchFrom m' a' n p = some w) : fetchFrom m a N p = some w := by
  unfold fetchFrom at h ⊢
  split at h
  · rename_i hin
    obtain ⟨hlt, h4⟩ := hin
    have hpa := p.toNat_lt
    have haa := a.toNat_lt
    have ha'n : a'.toNat = (a.toNat + 4 * o) % 2 ^ 64 := by
      rw [ha', UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hd : (p - a').toNat = (2 ^ 64 - a'.toNat + p.toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
    have hd2 : (p - a).toNat = (2 ^ 64 - a.toNat + p.toNat) % 2 ^ 64 := UInt64.toNat_sub _ _
    have hpa' : (p - a).toNat = (p - a').toNat + 4 * o := by
      have := a'.toNat_lt
      simp only [Nat.reducePow] at *
      omega
    rw [if_pos ⟨by omega, by omega⟩]
    rw [← h]
    have hk : ∀ k < 4, p + UInt64.ofNat k = a' + UInt64.ofNat ((p - a').toNat + k) := by
      intro k hk
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
      have := a'.toNat_lt
      simp only [Nat.reducePow] at *
      omega
    have hb : ∀ k < 4, m' (p + UInt64.ofNat k) = m (p + UInt64.ofNat k) := fun k hk' => by
      rw [hk k hk']
      exact hm _ (by omega)
    unfold load32
    have h0 := hb 0 (by decide)
    have h1 := hb 1 (by decide)
    have h2 := hb 2 (by decide)
    have h3 := hb 3 (by decide)
    rw [show p + UInt64.ofNat 0 = p by simp] at h0
    rw [show p + 1 = p + UInt64.ofNat 1 from rfl, show p + 2 = p + UInt64.ofNat 2 from rfl,
      show p + 3 = p + UInt64.ofNat 3 from rfl, h0, h1, h2, h3]
  · cases h

end LeanExe.A64
