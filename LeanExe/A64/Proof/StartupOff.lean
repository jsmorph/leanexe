import LeanExe.A64.Proof.Addr
import LeanExe.A64.Proof.ImageLayout
import LeanExe.A64.Proof.Lift
import LeanExe.A64.Proof.Table

/-!
The run of an image's entry and the startup's first part in the boot model: the header's
`MSR SPSel, #1` and its branch to the startup, then the startup's instructions 0 to 39, which end
with the `ISB` that puts the MMU's enable in effect.  While the MMU is off every fetch succeeds,
and `bootReach_of_reach_off` lifts the program model's runs of the instructions that touch no
memory, among them `addrOf` and `movImm`.  `OffAt` collects what the system instructions of this
part keep: SP_EL1, the MMU off, the memory, SP, and the UART's output.

`MRS X1, CurrentEL` reads 4 at EL1, so `B.NE` falls through, and `CBZ` on the field TCRX of
`ID_AA64MMFR3_EL1` skips the write of `TCR2_EL1` exactly when the processor lacks the register.
After the first `ISB`, `TLBI VMALLE1` and `DSB ISH` clean the TLBs, and the write of `sctlrOn`
changes only the field M of `SCTLR_EL1`, so the TLBs stay clean.  The last `ISB` is fetched while
the written registers have the MMU on, so the table must map its address as executable Normal
memory, which it does for an image in the RAM GiB.
-/

namespace LeanExe.A64

open Wasm

variable {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}

/-- With the MMU off, `addrOf`'s two instructions at `here` are two steps of the boot model by its
rule `plain`, which set register `d`, below 31, to the target and keep the other registers, SP,
the memory, and the output. -/
theorem boot_addrOf {b : Boot} {d : Fin 32} {here target : UInt64} {is : List Instr}
    (hg : addrOf d here target = .ok is) (hd : d.val < 31) (hc : CodeAt code here is)
    (hpc : b.core.pc = here) (hsp : b.spSel = true) (hoff : b.mmuOff) :
    ∃ c, BootReach h R code b { b with core := c } ∧ c.pc = after here 2 ∧ c.x d = target ∧
      (∀ q, q ≠ d → c.x q = b.core.x q) ∧ c.sp = b.core.sp ∧ c.mem = b.core.mem ∧
      c.out = b.core.out := by
  obtain ⟨c, hr, hp, hx, hk, hs, hm, ho⟩ := run_addrOf noMemory code hg hd hc hpc
  exact ⟨c, bootReach_of_reach_off hsp hoff hr ho, hp, hx, hk, hs, hm, ho⟩

/-- With the MMU off, the four instructions of `movImm d v` at `a` are four steps of the boot model
by its rule `plain`, which set register `d`, below 31, to `v` and keep the other registers, SP,
the memory, and the output. -/
theorem boot_movImm {b : Boot} {a : UInt64} {d : Fin 32} {v : UInt64} (hd : d.val < 31)
    (hcode : CodeAt code a (movImm d v)) (hpc : b.core.pc = a) (hsp : b.spSel = true)
    (hoff : b.mmuOff) :
    ∃ c, BootReach h R code b { b with core := c } ∧ c.pc = after a 4 ∧ c.x d = v ∧
      (∀ q, q ≠ d → c.x q = b.core.x q) ∧ c.sp = b.core.sp ∧ c.mem = b.core.mem ∧
      c.out = b.core.out := by
  obtain ⟨c, hr, hp, hx, hk, hs, hm, ho⟩ := run_movImm noMemory code hd hcode hpc
  exact ⟨c, bootReach_of_reach_off hsp hoff hr ho, hp, hx, hk, hs, hm, ho⟩

/-- With the MMU off, `MSR` of `r` from `Xt` writes `r` as `Xt` holds it. -/
theorem boot_msrOf {b : Boot} {r : SysReg} {t : Fin 32} {w : Sys}
    (hc : code b.core.pc = some (encode (msrOf r t))) (hsp : b.spSel = true) (hoff : b.mmuOff)
    (hw : b.written.set h r (b.core.x t) = some w) :
    BootStep h R code b { b with
      core := { b.core with pc := b.core.pc + 4 }
      written := w
      tlb := if keepsTlb r b.written w then b.tlb else .unknown } :=
  boot_sys hc (.inl hsp) hoff (by simp only [sysExec, msrOf, SysReg.ofCode_code, hw])

/-- `LSR X1, X1, #2`, `CMP X1, #1`, and `B.NE`, the startup's instructions 1 to 3, from a state
whose X1 holds 4, which `MRS X1, CurrentEL` reads at EL1: the branch falls through. -/
theorem run_checkEL {P : Platform} {s : State} {a : UInt64} {f : Fin 524288}
    (h1 : code (after a 1) = some (encode (.lsrImm 1 1 2)))
    (h2 : code (after a 2) = some (encode (.subsImm 31 1 1)))
    (h3 : code (after a 3) = some (encode (.bcond 1 f))) (hpc : s.pc = after a 1)
    (hx : s.x 1 = 4) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 4 ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.out = s.out := by
  let s1 : State := { s.setX 1 (s.x 1 >>> UInt64.ofNat (2 : Fin 64).val) with pc := s.pc + 4 }
  let s2 : State :=
    { s1.subs 31 (s1.xsp 1) (UInt64.ofNat (1 : Fin 4096).val) with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 2 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  have p2 : s2.pc = after a 3 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have e : s1.xsp 1 = 1 := by
    rw [State.xsp_eq_x (r := 1) (by decide)]
    show (s.setX 1 _).x 1 = 1
    rw [State.x_setX_same (r := 1) (by decide), hx]
    decide
  have hz : s2.condHolds 1 = false :=
    (congrArg (fun x : UInt64 => !(x - UInt64.ofNat (1 : Fin 4096).val == 0)) e).trans
      (by decide)
  have e3 : exec P (.bcond 1 f) s2 = some { s2 with pc := s2.pc + 4 } := by
    show some { s2 with pc := if s2.condHolds 1 then _ else _ } = _
    rw [hz, ite_eq_right Bool.false_ne_true]
  refine ⟨{ s2 with pc := s2.pc + 4 },
    reach_exec P code (i := .lsrImm 1 1 2) (by rw [hpc]; exact h1) rfl
      (reach_exec P code (i := .subsImm 31 1 1) (by rw [p1]; exact h2) rfl
        (reach_exec P code (i := .bcond 1 f) (by rw [p2]; exact h3) e3 (.refl _))),
    by show s2.pc + 4 = _; rw [p2, ← after_succ], ?_, ?_, ?_⟩ <;>
    simp [s2, s1, State.subs]

/-- `MOVZ X2, #15`, `AND X1, X1, X2`, and `CBZ X1` to instruction 31, the startup's
instructions 27 to 29: the run reaches instruction 31 when the low four bits of X1, the field
TCRX of `ID_AA64MMFR3_EL1` after `MRS`, are 0, and instruction 30 otherwise. -/
theorem run_mmfr3 {P : Platform} {s : State} {a : UInt64} {f : Fin 524288}
    (h27 : code (after a 27) = some (encode (.movz 2 15 0)))
    (h28 : code (after a 28) = some (encode (.andReg 1 1 2)))
    (h29 : code (after a 29) = some (encode (.cbz 1 f)))
    (hf : cbField (after a 29) (after a 31) = .ok f) (hpc : s.pc = after a 27) :
    ∃ s', Reach P code s s' ∧
      s'.pc = (if s.x 1 &&& 15 = 0 then after a 31 else after a 30) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.out = s.out := by
  let v2 : UInt64 := UInt64.ofNat (15 : Fin 65536).val <<< UInt64.ofNat (16 * (0 : Fin 4).val)
  let s1 : State := { s.setX 2 v2 with pc := s.pc + 4 }
  let s2 : State := { s1.setX 1 (s1.x 1 &&& s1.x 2) with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 28 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  have p2 : s2.pc = after a 29 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have e15 : v2 = 15 := by decide
  have x2 : s2.x 1 = s.x 1 &&& 15 := by
    show (s1.setX 1 (s1.x 1 &&& s1.x 2)).x 1 = _
    rw [State.x_setX_same (r := 1) (by decide)]
    show (s.setX 2 v2).x 1 &&& (s.setX 2 v2).x 2 = _
    rw [State.x_setX_ne (r := 2) (q := 1) (by decide), State.x_setX_same (r := 2) (by decide),
      e15]
  refine ⟨{ s2 with pc := if s2.x 1 = 0 then s2.pc + sext 19 f.val * 4 else s2.pc + 4 },
    reach_exec P code (i := .movz 2 15 0) (by rw [hpc]; exact h27) rfl
      (reach_exec P code (i := .andReg 1 1 2) (by rw [p1]; exact h28) rfl
        (reach_exec P code (i := .cbz 1 f) (by rw [p2]; exact h29) rfl (.refl _))),
    ?_, ?_, ?_, ?_⟩
  · show (if s2.x 1 = 0 then s2.pc + sext 19 f.val * 4 else s2.pc + 4) = _
    rw [x2, p2, cbField_target hf, ← after_succ]
  all_goals simp [s2, s1]

/-- A state `b` of the startup's first part, reached from `b0`, at `a` and with the written system
registers `w`: SP_EL1 is the stack pointer, the MMU is off in both copies of `SCTLR_EL1`, and the
memory, SP, and UART's output are `b0`'s. -/
structure OffAt (b0 : Boot) (a : UInt64) (w : Sys) (b : Boot) : Prop where
  pc : b.core.pc = a
  spSel : b.spSel = true
  off : b.mmuOff
  written : b.written = w
  mem : b.core.mem = b0.core.mem
  sp : b.core.sp = b0.core.sp
  out : b.core.out = b0.core.out

/-- A run of the boot model that changes only the core of a state of the startup's first part,
and keeps its memory, SP, and output, ends in such a state. -/
theorem OffAt.core {b0 b : Boot} {a a' : UInt64} {w : Sys} {c : State}
    (hb : BootReach h R code b0 b) (ho : OffAt b0 a w b)
    (hr : BootReach h R code b { b with core := c }) (hpc : c.pc = a')
    (hm : c.mem = b.core.mem) (hs : c.sp = b.core.sp) (hout : c.out = b.core.out) :
    BootReach h R code b0 { b with core := c } ∧ OffAt b0 a' w { b with core := c } :=
  ⟨hb.trans hr, hpc, ho.spSel, ho.off, ho.written, hm.trans ho.mem, hs.trans ho.sp,
    hout.trans ho.out⟩

/-- `MRS Xt` of `r`, with `t` below 31, at instruction `k` from a state of the startup's first
part. -/
theorem OffAt.mrs {b0 b : Boot} {a : UInt64} {k : Nat} {w : Sys} {t : Fin 32} {r : SysReg}
    {v : UInt64} (hb : BootReach h R code b0 b) (ho : OffAt b0 (after a k) w b)
    (ht : t.val < 31) (hc : code (after a k) = some (encode (mrsOf t r)))
    (he : sysExec h (mrsOf t r) b =
      some { b with core := ({ b.core with pc := b.core.pc + 4 } : State).setX t v }) :
    ∃ b', BootReach h R code b0 b' ∧ OffAt b0 (after a (k + 1)) w b' ∧ b'.core.x t = v := by
  obtain ⟨hpc, hsp, hoff, hw, hm, hs, hout⟩ := ho
  refine ⟨_, hb.trans (.single (boot_sys (by rw [hpc]; exact hc) (.inl hsp) hoff he)),
    ⟨?_, hsp, hoff, hw, ?_, ?_, ?_⟩, State.x_setX_same ht⟩
  · show (({ b.core with pc := b.core.pc + 4 } : State).setX t v).pc = _
    rw [State.setX_pc]
    show b.core.pc + 4 = _
    rw [hpc, ← after_succ]
  · show (({ b.core with pc := b.core.pc + 4 } : State).setX t v).mem = _
    rw [State.setX_mem]
    exact hm
  · show (({ b.core with pc := b.core.pc + 4 } : State).setX t v).sp = _
    rw [State.setX_sp]
    exact hs
  · show (({ b.core with pc := b.core.pc + 4 } : State).setX t v).out = _
    rw [State.setX_out]
    exact hout

/-- `MSR` of `r` from `Xt` at instruction `k` from a state of the startup's first part, which
writes a value of `SCTLR_EL1` with the MMU off. -/
theorem OffAt.msr {b0 b : Boot} {a : UInt64} {k : Nat} {w w' : Sys} {r : SysReg} {t : Fin 32}
    (hb : BootReach h R code b0 b) (ho : OffAt b0 (after a k) w b)
    (hc : code (after a k) = some (encode (msrOf r t))) (hw : w.set h r (b.core.x t) = some w')
    (hoff : w'.sctlr &&& 1 = 0) :
    ∃ b', BootReach h R code b0 b' ∧ OffAt b0 (after a (k + 1)) w' b' := by
  obtain ⟨hpc, hsp, hmo, hwb, hm, hs, hout⟩ := ho
  subst hwb
  refine ⟨_, hb.trans (.single (boot_msrOf (by rw [hpc]; exact hc) hsp hmo hw)),
    ?_, hsp, ⟨hmo.1, hoff⟩, rfl, hm, hs, hout⟩
  show b.core.pc + 4 = _
  rw [hpc, ← after_succ]

/-- The startup's instructions 31 to 39 from a state of its first part whose written registers
hold the covered configuration but for `SCTLR_EL1`, which holds `sctlrOn - 1`.  `ISB` puts the
written registers in effect, `TLBI VMALLE1` and `DSB ISH` clean the TLBs and complete the stores
to the UART, `MSR SCTLR_EL1` writes `sctlrOn`, which keeps the TLBs clean, and the last `ISB` puts
it in effect.  That `ISB` is fetched with the MMU on in the written registers, so its address
must lie in the RAM GiB of the table in memory. -/
theorem OffAt.mmuOn {b0 b : Boot} {a : UInt64} {w : Sys}
    (hb : BootReach h R code b0 b) (ho : OffAt b0 (after a 31) w b)
    (h31 : code (after a 31) = some (encode .isb))
    (h32 : code (after a 32) = some (encode .tlbiVmalle1))
    (h33 : code (after a 33) = some (encode .dsbIsh))
    (h34 : CodeAt code (after a 34) (movImm 1 sctlrOn))
    (h38 : code (after a 38) = some (encode (msrOf .sctlr 1)))
    (h39 : code (after a 39) = some (encode .isb))
    (hw : w.sctlr = sctlrOn - 1) (hcov : { w with sctlr := sctlrOn }.covered h = true)
    (htab : ∀ j (hj : j < 32), b0.core.mem (w.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (ha : 0x40000000 ≤ after a 39) (ha' : after a 39 < 0x80000000) :
    ∃ b', BootReach h R code b0 b' ∧ b'.core.pc = after a 40 ∧ b'.spSel = true ∧
      b'.written = b'.eff ∧ b'.tlb = .clean ∧ b'.eff = { w with sctlr := sctlrOn } ∧
      b'.core.mem = b0.core.mem ∧ b'.core.sp = b0.core.sp ∧ b'.core.out = b0.core.out ∧
      b'.uartDone = true := by
  obtain ⟨hpc, hsp, hoff, hwb, hm, hs, hout⟩ := ho
  subst hwb
  let b32 : Boot := { b with core := { b.core with pc := b.core.pc + 4 }, eff := b.written }
  have off32 : b32.mmuOff := ⟨hoff.2, hoff.2⟩
  have p32 : b32.core.pc = after a 32 := by
    show b.core.pc + 4 = _
    rw [hpc, ← after_succ]
  have s31 : BootStep h R code b b32 :=
    boot_sys (i := .isb) (by rw [hpc]; exact h31) (.inl hsp) hoff rfl
  let b33 : Boot := { b32 with core := { b32.core with pc := b32.core.pc + 4 }, tlb := .pending }
  have p33 : b33.core.pc = after a 33 := by
    show b32.core.pc + 4 = _
    rw [p32, ← after_succ]
  have s32 : BootStep h R code b32 b33 := by
    refine boot_sys (i := .tlbiVmalle1) (by rw [p32]; exact h32) (.inl hsp) off32 ?_
    show some { b32 with
        core := b33.core
        tlb := if b.written = b.written then .pending else .unknown } =
      some { b32 with core := b33.core, tlb := .pending }
    rw [ite_eq_left rfl]
  let b34 : Boot :=
    { b33 with core := { b33.core with pc := b33.core.pc + 4 }, tlb := .clean, uartDone := true }
  have p34 : b34.core.pc = after a 34 := by
    show b33.core.pc + 4 = _
    rw [p33, ← after_succ]
  have s33 : BootStep h R code b33 b34 :=
    boot_sys (i := .dsbIsh) (by rw [p33]; exact h33) (.inl hsp) off32 rfl
  obtain ⟨c, rc, pc, xc, -, sc, mc, oc⟩ :=
    boot_movImm (h := h) (R := R) (b := b34) (by decide) h34 p34 hsp off32
  rw [after_after] at pc
  let b39 : Boot :=
    { b34 with core := { c with pc := c.pc + 4 }, written := { b.written with sctlr := sctlrOn } }
  have p39 : b39.core.pc = after a 39 := by
    show c.pc + 4 = _
    rw [pc, ← after_succ]
  have hk : keepsTlb .sctlr b.written { b.written with sctlr := sctlrOn } = true := by
    show (b.written.sctlr ||| 1 == sctlrOn ||| 1) = true
    rw [hw]
    decide
  have s38 : BootStep h R code { b34 with core := c } b39 := by
    have := boot_msrOf (h := h) (R := R) (b := { b34 with core := c }) (r := .sctlr) (t := 1)
      (w := { b.written with sctlr := sctlrOn }) (by rw [pc]; exact h38) hsp off32
      (by rw [xc]; rfl)
    rw [hk] at this
    exact this
  have hf : fetchOk h b39.written b39.tlb b39.core.mem b39.core.pc :=
    .inr ⟨rfl, true, classify_normal hcov
      (fun j hj => (congrFun (mc.trans hm) _).trans (htab j hj))
      (by rw [p39]; exact ha) (by rw [p39]; exact ha')⟩
  have s39 : BootStep h R code b39
      { b39 with core := { b39.core with pc := b39.core.pc + 4 }, eff := b39.written } :=
    .sys (i := .isb) (by rw [p39]; exact h39) (decode_encode _) (.inl hsp) (.inl hoff.2) hf rfl
  refine ⟨_, hb.trans (.next s31 (.next s32 (.next s33 (rc.trans (.next s38 (.single s39)))))),
    ?_, hsp, rfl, rfl, rfl, mc.trans hm, sc.trans hs, oc.trans hout, rfl⟩
  show c.pc + 4 + 4 = _
  rw [pc, ← after_succ, ← after_succ]

/-- The run of an image's entry and of the startup's instructions 0 to 39 in the boot model, for
an image at a multiple of 4096 in the RAM GiB.  From the entry with the MMU off and the image's
translation table in memory, the machine selects SP_EL1, branches to the startup, finds itself at
EL1, and turns the MMU on, whether or not the processor has `TCR2_EL1`.  It ends with the written
system registers in effect in the covered configuration, the table at `TTBR0_EL1`, clean TLBs, and
every store to the UART complete, and it changes no byte of memory, SP, or the UART's output. -/
theorem boot_startupOff {image : UInt64} {n : Nat} {m : Module} {cap : Nat} {room : UInt64}
    {is : List Instr} {b : Boot} (himg : image.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ image.toNat)
    (hhi : image.toNat + (layoutOf image n m cap room).size ≤ 0x80000000)
    (hs : startupCode (layoutOf image n m cap room) = .ok is)
    (hhead : CodeAt code image [.spsel1, .b 15]) (hcode : CodeAt code (image + 64) is)
    (hpc : b.core.pc = image) (hoff : b.mmuOff)
    (htab : ∀ j (hj : j < 32),
      b.core.mem ((layoutOf image n m cap room).table + UInt64.ofNat j) = tableBytes[j]) :
    ∃ b', BootReach h R code b b' ∧ b'.core.pc = after (image + 64) 40 ∧ b'.spSel = true ∧
      b'.written = b'.eff ∧ b'.tlb = .clean ∧ b'.eff.covered h = true ∧
      b'.eff.ttbr0 = (layoutOf image n m cap room).table ∧ b'.core.mem = b.core.mem ∧
      b'.core.sp = b.core.sp ∧ b'.core.out = b.core.out ∧ b'.uartDone = true := by
  have hao := areaOff_ge n
  have hdv : 2048 ∣ vecOff n := roundUp_dvd _ _
  rw [(layoutOf_fields image n m cap room).2.2.2.2.2.2.2.2] at hhi
  have hT : (layoutOf image n m cap room).table.toNat = image.toNat + tabOff n := by
    rw [(layoutOf_fields image n m cap room).2.2.2.1, UInt64.toNat_add,
      toNat_ofNat_lt (n := tabOff n) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hT32 : (layoutOf image n m cap room).table % 32 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, hT]
    show (image.toNat + tabOff n) % 32 = 0
    unfold tabOff
    omega
  have hTlt : (layoutOf image n m cap room).table < 0x100000000 := by
    rw [UInt64.lt_iff_toNat_lt, hT]
    show _ < 4294967296
    omega
  have h220 : (after (image + 64) 39).toNat = image.toNat + 220 := by
    rw [after, UInt64.add_assoc, show (64 : UInt64) + 4 * UInt64.ofNat 39 = 220 by decide,
      UInt64.toNat_add]
    show (image.toNat + 220) % 2 ^ 64 = _
    omega
  have ha39 : 0x40000000 ≤ after (image + 64) 39 := by
    rw [UInt64.le_iff_toNat_le, h220]
    show 1073741824 ≤ _
    omega
  have ha39' : after (image + 64) 39 < 0x80000000 := by
    rw [UInt64.lt_iff_toNat_lt, h220]
    show _ < 2147483648
    unfold tabOff at hao
    omega
  generalize hL : layoutOf image n m cap room = L at hs htab hT32 hTlt ⊢
  have hLi : L.image = image := by
    subst hL
    rfl
  obtain ⟨_, skip, vec, tab, _, _, _, _, _, _, -, hskip, hvec, htc, -, -, -, -, -, -, his⟩ :=
    startupCode_ok hs
  rw [hLi] at hskip hvec htc
  rw [his] at hcode
  generalize hs0 : image + 64 = s at hcode hskip hvec htc ha39 ha39' ⊢
  iterate 11 replace hcode := ((CodeAt.append (code := code)).mp hcode).1
  have hm4 : ∀ d v, (movImm d v).length = 4 := fun _ _ => rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append, CodeAt.append, CodeAt.cons,
    after_after, addrOf_length hvec, addrOf_length htc, hm4, Nat.reduceAdd] at hcode
  obtain ⟨c0, c1, c2, c3, cv, c6, cm7, c11, c12, cm13, c17, cm18, c22, ct, c25, c26, c27, c28,
    c29, c30, c31, c32, c33, cm34, c38, c39, -⟩ := hcode
  have hh0 := hhead 0 (by decide)
  have hh1 := hhead 1 (by decide)
  rw [after_zero] at hh0
  rw [after_succ, after_zero] at hh1
  have e64 : b.core.pc + 4 + sext 26 (15 : Fin 67108864).val * 4 = s := by
    rw [hpc, ← hs0, UInt64.add_assoc,
      show (4 : UInt64) + sext 26 (15 : Fin 67108864).val * 4 = 64 by decide]
  obtain ⟨b1, r1, o1⟩ : ∃ b1, BootReach h R code b b1 ∧ OffAt b (after s 0) b.written b1 :=
    ⟨_, .next (boot_sys (i := .spsel1) (by rw [hpc]; exact hh0) (.inr rfl) hoff rfl)
      (.single (boot_plain (i := .b 15) (by rw [hpc]; exact hh1) rfl hoff rfl rfl
        (congrArg (fun p : UInt64 => some ({ b.core with pc := p } : State)) e64))),
      (after_zero s).symm, rfl, hoff, rfl, rfl, rfl, rfl⟩
  rw [← after_zero s] at c0
  have hS : sctlrOn - 1 &&& 1 = 0 := by decide
  obtain ⟨b2, r2, o2, x2⟩ := OffAt.mrs r1 o1 (by decide) c0 rfl
  obtain ⟨d3, q3, p3, sp3, m3, out3⟩ := run_checkEL (P := noMemory) c1 c2 c3 o2.pc x2
  obtain ⟨d5, q5, p5, x5, -, sp5, m5, out5⟩ := run_addrOf noMemory code hvec (by decide) cv p3
  obtain ⟨r5, o5⟩ := OffAt.core r2 o2
    (bootReach_of_reach_off o2.spSel o2.off (q3.trans q5) (out5.trans out3))
    (p5.trans (after_after _ _ _)) (m5.trans m3) (sp5.trans sp3) (out5.trans out3)
  obtain ⟨b6, r6, o6⟩ := OffAt.msr r5 o5 c6 (w' := { b.written with vbar := L.vectors })
    (by rw [x5]; rfl) hoff.2
  obtain ⟨d10, q10, p10, x10, -, sp10, m10, out10⟩ :=
    boot_movImm (h := h) (R := R) (by decide) cm7 o6.pc o6.spSel o6.off
  obtain ⟨r10, o10⟩ := OffAt.core r6 o6 q10 (p10.trans (after_after _ _ _)) m10 sp10 out10
  obtain ⟨b11, r11, o11⟩ := OffAt.msr r10 o10 c11
    (w' := { b.written with vbar := L.vectors, sctlr := sctlrOn - 1 }) (by rw [x10]; rfl) hS
  obtain ⟨b12, r12, o12⟩ := OffAt.msr r11 o11 c12
    (w' := { b.written with vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := 0 }) rfl hS
  obtain ⟨d16, q16, p16, x16, -, sp16, m16, out16⟩ :=
    boot_movImm (h := h) (R := R) (by decide) cm13 o12.pc o12.spSel o12.off
  obtain ⟨r16, o16⟩ := OffAt.core r12 o12 q16 (p16.trans (after_after _ _ _)) m16 sp16 out16
  obtain ⟨b17, r17, o17⟩ := OffAt.msr r16 o16 c17
    (w' := { b.written with
      vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := 0, mair := mairValue })
    (by rw [x16]; rfl) hS
  obtain ⟨d21, q21, p21, x21, -, sp21, m21, out21⟩ :=
    boot_movImm (h := h) (R := R) (by decide) cm18 o17.pc o17.spSel o17.off
  obtain ⟨r21, o21⟩ := OffAt.core r17 o17 q21 (p21.trans (after_after _ _ _)) m21 sp21 out21
  obtain ⟨b22, r22, o22⟩ := OffAt.msr r21 o21 c22
    (w' := { b.written with
      vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := 0, mair := mairValue, tcr := tcrValue })
    (by rw [x21]; rfl) hS
  obtain ⟨d24, q24, p24, x24, -, sp24, m24, out24⟩ :=
    boot_addrOf (h := h) (R := R) htc (by decide) ct o22.pc o22.spSel o22.off
  obtain ⟨r24, o24⟩ := OffAt.core r22 o22 q24 (p24.trans (after_after _ _ _)) m24 sp24 out24
  obtain ⟨b25, r25, o25⟩ := OffAt.msr r24 o24 c25
    (w' := { b.written with
      vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := 0, mair := mairValue, tcr := tcrValue,
      ttbr0 := L.table })
    (by rw [x24]; rfl) hS
  obtain ⟨b26, r26, o26, x26⟩ := OffAt.mrs r25 o25 (by decide) c26 rfl
  obtain ⟨d29, q29, p29, sp29, m29, out29⟩ :=
    run_mmfr3 (P := noMemory) c27 c28 c29 hskip o26.pc
  rw [x26] at p29
  obtain ⟨r29, o29⟩ := OffAt.core r26 o26
    (bootReach_of_reach_off o26.spSel o26.off q29 out29) p29 m29 sp29 out29
  obtain ⟨w, b31, r31, o31, hw31, hcov31, hT31⟩ : ∃ w b31, BootReach h R code b b31 ∧
      OffAt b (after s 31) w b31 ∧ w.sctlr = sctlrOn - 1 ∧
      { w with sctlr := sctlrOn }.covered h = true ∧ w.ttbr0 = L.table := by
    cases ht : h.tcrx
    · have hz : h.mmfr3 &&& 15 = 0 := by simpa [Hw.tcrx] using ht
      rw [ite_eq_left hz] at o29
      exact ⟨_, _, r29, o29, rfl, by simp [Sys.covered, ht, hT32, hTlt], rfl⟩
    · have hz : ¬ h.mmfr3 &&& 15 = 0 := by simpa [Hw.tcrx] using ht
      rw [ite_eq_right hz] at o29
      obtain ⟨b30, r30, o30⟩ := OffAt.msr r29 o29 c30
        (w' := { b.written with
          vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := 0, mair := mairValue,
          tcr := tcrValue, ttbr0 := L.table, tcr2 := 0 })
        (by show (if h.tcrx then some _ else none) = _; exact (ite_eq_left ht).trans rfl)
        hS
      exact ⟨_, _, r30, o30, rfl, by simp [Sys.covered, ht, hT32, hTlt], rfl⟩
  obtain ⟨bf, rf, pf, spf, wef, tlbf, eff, mf, sf, of, uf⟩ :=
    OffAt.mmuOn r31 o31 c31 c32 c33 cm34 c38 c39 hw31 hcov31
      (fun j hj => by rw [hT31]; exact htab j hj) ha39 ha39'
  exact ⟨bf, rf, pf, spf, wef, tlbf, by rw [eff]; exact hcov31, by rw [eff]; exact hT31, mf, sf,
    of, uf⟩

end LeanExe.A64
