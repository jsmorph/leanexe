import LeanExe.A64.Proof.Addr
import LeanExe.A64.Proof.ImageLayout
import LeanExe.A64.Proof.Lift
import LeanExe.A64.Proof.Table

/-!
The run of an image's entry and the startup's first part in the boot model: the header's
`MSR SPSel, #1` and its branch to the startup, then the startup's instructions 0 to 42, which end
with the `ISB` that puts the MMU's enable in effect.  While the MMU is off every fetch succeeds,
and `bootReach_of_reach_off` lifts the program model's runs of the instructions that touch no
memory, among them `addrOf`, `movImm`, and `MOVZ`.  `OffAt` collects what the system instructions
of this part keep: SP_EL1, the MMU off, the memory, SP, and the UART's output.

`MRS X1, CurrentEL` reads 4 at EL1, so `B.NE` falls through, and `CBZ` on the field TCRX of
`ID_AA64MMFR3_EL1` skips the write of `TCR2_EL1` exactly when the processor lacks the register.
The write of `cpacrValue` to `CPACR_EL1` enables floating point.  After the first `ISB`,
`TLBI VMALLE1` and `DSB ISH` clean the TLBs, `MSR FPCR`, which the effective `CPACR_EL1` permits,
writes `fpcrValue`, and the write of `sctlrOn` changes only the field M of `SCTLR_EL1`, so the TLBs
stay clean.  The last `ISB` is fetched while
the written registers have the MMU on, so the table must map its address as executable Normal
memory, which it does for an image in the RAM GiB.
-/

namespace LeanExe.A64

open Wasm

variable {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}

/-- With the MMU off, `addrOf`'s two instructions at `here` are two steps of the boot model by its
rule `plain`, which set register `d`, below 31, to the target and keep the other registers, SP,
the memory, and the output, when the code map's addresses and the next address lie below
2^55. -/
theorem boot_addrOf (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {b : Boot} {d : Fin 32}
    {here target : UInt64} {is : List Instr}
    (hg : addrOf d here target = .ok is) (hd : d.val < 31) (hc : CodeAt code here is)
    (hpc : b.core.pc = here) (hsp : b.spSel = true) (hoff : b.mmuOff)
    (hend : (after here 2).toNat < 2 ^ 55) :
    ∃ c, BootReach h R code b { b with core := c } ∧ c.pc = after here 2 ∧ c.x d = target ∧
      (∀ q, q ≠ d → c.x q = b.core.x q) ∧ c.sp = b.core.sp ∧ c.mem = b.core.mem ∧
      c.out = b.core.out := by
  obtain ⟨c, hr, hp, hx, hk, hs, hm, ho⟩ := run_addrOf noMemory code hg hd hc hpc
  exact ⟨c, bootReach_of_reach_off hdom hsp hoff hr ho (by rw [hp]; exact hend), hp, hx, hk, hs,
    hm, ho⟩

/-- With the MMU off, the four instructions of `movImm d v` at `a` are four steps of the boot model
by its rule `plain`, which set register `d`, below 31, to `v` and keep the other registers, SP,
the memory, and the output, when the code map's addresses and the next address lie below
2^55. -/
theorem boot_movImm (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {b : Boot} {a : UInt64}
    {d : Fin 32} {v : UInt64} (hd : d.val < 31)
    (hcode : CodeAt code a (movImm d v)) (hpc : b.core.pc = a) (hsp : b.spSel = true)
    (hoff : b.mmuOff) (hend : (after a 4).toNat < 2 ^ 55) :
    ∃ c, BootReach h R code b { b with core := c } ∧ c.pc = after a 4 ∧ c.x d = v ∧
      (∀ q, q ≠ d → c.x q = b.core.x q) ∧ c.sp = b.core.sp ∧ c.mem = b.core.mem ∧
      c.out = b.core.out := by
  obtain ⟨c, hr, hp, hx, hk, hs, hm, ho⟩ := run_movImm noMemory code hd hcode hpc
  exact ⟨c, bootReach_of_reach_off hdom hsp hoff hr ho (by rw [hp]; exact hend), hp, hx, hk, hs,
    hm, ho⟩

/-- With the MMU off, `MSR` of `r` from `Xt`, when it does not trap, writes `r` as `Xt` holds
it. -/
theorem boot_msrOf {b : Boot} {r : SysReg} {t : Fin 32} {w : Sys}
    (hc : code b.core.pc = some (encode (msrOf r t))) (hsp : b.spSel = true) (hoff : b.mmuOff)
    (htr : b.msrTraps r = false) (hw : b.written.set h r (b.core.x t) = some w) :
    BootStep h R code b { b with
      core := { b.core with pc := b.core.pc + 4 }
      written := w
      tlb := if keepsTlb r b.written w then b.tlb else .unknown } :=
  boot_sys hc (.inl hsp) hoff (by
    simp only [sysExec, msrOf, SysReg.ofCode_code, htr, hw, Bool.false_eq_true, ↓reduceIte])

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

/-- `MOVZ X2, #15`, `AND X1, X1, X2`, and `CBZ X1` to instruction 32, the startup's
instructions 28 to 30: the run reaches instruction 32 when the low four bits of X1, the field
TCRX of `ID_AA64MMFR3_EL1` after `MRS`, are 0, and instruction 31 otherwise. -/
theorem run_mmfr3 {P : Platform} {s : State} {a : UInt64} {f : Fin 524288}
    (h28 : code (after a 28) = some (encode (.movz 2 15 0)))
    (h29 : code (after a 29) = some (encode (.andReg 1 1 2)))
    (h30 : code (after a 30) = some (encode (.cbz 1 f)))
    (hf : cbField (after a 30) (after a 32) = .ok f) (hpc : s.pc = after a 28) :
    ∃ s', Reach P code s s' ∧
      s'.pc = (if s.x 1 &&& 15 = 0 then after a 32 else after a 31) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.out = s.out := by
  let v2 : UInt64 := UInt64.ofNat (15 : Fin 65536).val <<< UInt64.ofNat (16 * (0 : Fin 4).val)
  let s1 : State := { s.setX 2 v2 with pc := s.pc + 4 }
  let s2 : State := { s1.setX 1 (s1.x 1 &&& s1.x 2) with pc := s1.pc + 4 }
  have p1 : s1.pc = after a 29 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  have p2 : s2.pc = after a 30 := by
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
    reach_exec P code (i := .movz 2 15 0) (by rw [hpc]; exact h28) rfl
      (reach_exec P code (i := .andReg 1 1 2) (by rw [p1]; exact h29) rfl
        (reach_exec P code (i := .cbz 1 f) (by rw [p2]; exact h30) rfl (.refl _))),
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
does not trap and writes a value of `SCTLR_EL1` with the MMU off. -/
theorem OffAt.msr {b0 b : Boot} {a : UInt64} {k : Nat} {w w' : Sys} {r : SysReg} {t : Fin 32}
    (hb : BootReach h R code b0 b) (ho : OffAt b0 (after a k) w b)
    (hc : code (after a k) = some (encode (msrOf r t))) (htr : b.msrTraps r = false)
    (hw : w.set h r (b.core.x t) = some w') (hoff : w'.sctlr &&& 1 = 0) :
    ∃ b', BootReach h R code b0 b' ∧ OffAt b0 (after a (k + 1)) w' b' := by
  obtain ⟨hpc, hsp, hmo, hwb, hm, hs, hout⟩ := ho
  subst hwb
  refine ⟨_, hb.trans (.single (boot_msrOf (by rw [hpc]; exact hc) hsp hmo htr hw)),
    ?_, hsp, ⟨hmo.1, hoff⟩, rfl, hm, hs, hout⟩
  show b.core.pc + 4 = _
  rw [hpc, ← after_succ]

/-- `MOVZ Xd`, with `d` below 31, at instruction `k` from a state of the startup's first part,
when the next address lies below 2^55. -/
theorem OffAt.movz {b0 b : Boot} {a : UInt64} {k : Nat} {w : Sys} {d : Fin 32}
    {imm : Fin 65536} {hw : Fin 4} (hb : BootReach h R code b0 b) (ho : OffAt b0 (after a k) w b)
    (hd : d.val < 31) (hc : code (after a k) = some (encode (.movz d imm hw)))
    (hn : (after a (k + 1)).toNat < 2 ^ 55) :
    ∃ b', BootReach h R code b0 b' ∧ OffAt b0 (after a (k + 1)) w b' ∧
      b'.core.x d = UInt64.ofNat imm.val <<< UInt64.ofNat (16 * hw.val) := by
  obtain ⟨hpc, hsp, hoff, hwb, hm, hs, hout⟩ := ho
  let c : State :=
    { b.core.setX d (UInt64.ofNat imm.val <<< UInt64.ofNat (16 * hw.val)) with pc := b.core.pc + 4 }
  have hp : c.pc = after a (k + 1) := by
    show b.core.pc + 4 = _
    rw [hpc, ← after_succ]
  refine ⟨{ b with core := c },
    hb.trans (.single (boot_plain (i := .movz d imm hw) (c := c) (by rw [hpc]; exact hc) hsp hoff
      rfl rfl rfl (by rw [hp]; exact hn))),
    ⟨hp, hsp, hoff, hwb, ?_, ?_, ?_⟩, State.x_setX_same hd⟩
  · show (b.core.setX d _).mem = _
    rw [State.setX_mem]
    exact hm
  · show (b.core.setX d _).sp = _
    rw [State.setX_sp]
    exact hs
  · show (b.core.setX d _).out = _
    rw [State.setX_out]
    exact hout

/-- The startup's instructions 32 to 42 from a state of its first part whose written registers
hold the covered configuration but for `SCTLR_EL1`, which holds `sctlrOn - 1`, and `FPCR`.  `ISB`
puts the written registers in effect, `TLBI VMALLE1` and `DSB ISH` clean the TLBs and complete the
stores to the UART, `MOVZ` and `MSR FPCR` write `fpcrValue`, which the effective `CPACR_EL1`
permits, `MSR SCTLR_EL1` writes `sctlrOn`, and neither write changes what the TLBs may hold.  The
last `ISB` puts both writes in effect.  It is fetched with the MMU on in the written registers, so
its address must lie in the RAM GiB of the table in memory. -/
theorem OffAt.mmuOn (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {b0 b : Boot}
    {a : UInt64} {w : Sys} (hb : BootReach h R code b0 b) (ho : OffAt b0 (after a 32) w b)
    (h32 : code (after a 32) = some (encode .isb))
    (h33 : code (after a 33) = some (encode .tlbiVmalle1))
    (h34 : code (after a 34) = some (encode .dsbIsh))
    (h35 : code (after a 35) = some (encode (.movz 1 0x200 1)))
    (h36 : code (after a 36) = some (encode (msrOf .fpcr 1)))
    (h37 : CodeAt code (after a 37) (movImm 1 sctlrOn))
    (h41 : code (after a 41) = some (encode (msrOf .sctlr 1)))
    (h42 : code (after a 42) = some (encode .isb))
    (hw : w.sctlr = sctlrOn - 1) (hcp : w.cpacr = cpacrValue)
    (hcov : { w with sctlr := sctlrOn, fpcr := fpcrValue }.covered h = true)
    (htab : ∀ j (hj : j < 32), b0.core.mem (w.ttbr0 + UInt64.ofNat j) = tableBytes[j])
    (ha : 0x40000000 ≤ after a 42) (ha' : after a 42 < 0x80000000) :
    ∃ b', BootReach h R code b0 b' ∧ b'.core.pc = after a 43 ∧ b'.spSel = true ∧
      b'.written = b'.eff ∧ b'.tlb = .clean ∧
      b'.eff = { w with sctlr := sctlrOn, fpcr := fpcrValue } ∧
      b'.core.mem = b0.core.mem ∧ b'.core.sp = b0.core.sp ∧ b'.core.out = b0.core.out ∧
      b'.uartDone = true := by
  obtain ⟨hpc, hsp, hoff, hwb, hm, hs, hout⟩ := ho
  subst hwb
  let b33 : Boot := { b with core := { b.core with pc := b.core.pc + 4 }, eff := b.written }
  have off33 : b33.mmuOff := ⟨hoff.2, hoff.2⟩
  have p33 : b33.core.pc = after a 33 := by
    show b.core.pc + 4 = _
    rw [hpc, ← after_succ]
  have s32 : BootStep h R code b b33 :=
    boot_sys (i := .isb) (by rw [hpc]; exact h32) (.inl hsp) hoff rfl
  let b34 : Boot := { b33 with core := { b33.core with pc := b33.core.pc + 4 }, tlb := .pending }
  have p34 : b34.core.pc = after a 34 := by
    show b33.core.pc + 4 = _
    rw [p33, ← after_succ]
  have s33 : BootStep h R code b33 b34 := by
    refine boot_sys (i := .tlbiVmalle1) (by rw [p33]; exact h33) (.inl hsp) off33 ?_
    show some { b33 with
        core := b34.core
        tlb := if b.written = b.written then .pending else .unknown } =
      some { b33 with core := b34.core, tlb := .pending }
    rw [ite_eq_left rfl]
  let b35 : Boot :=
    { b34 with core := { b34.core with pc := b34.core.pc + 4 }, tlb := .clean, uartDone := true }
  have p35 : b35.core.pc = after a 35 := by
    show b34.core.pc + 4 = _
    rw [p34, ← after_succ]
  have s34 : BootStep h R code b34 b35 :=
    boot_sys (i := .dsbIsh) (by rw [p34]; exact h34) (.inl hsp) off33 rfl
  let v : UInt64 := UInt64.ofNat (0x200 : Fin 65536).val <<< UInt64.ofNat (16 * (1 : Fin 4).val)
  have ev : v = fpcrValue := by decide
  let b36 : Boot := { b35 with core := { b35.core.setX 1 v with pc := b35.core.pc + 4 } }
  have p36 : b36.core.pc = after a 36 := by
    show b35.core.pc + 4 = _
    rw [p35, ← after_succ]
  have s35 : BootStep h R code b35 b36 :=
    boot_plain (i := .movz 1 0x200 1) (c := b36.core) (by rw [p35]; exact h35) hsp off33 rfl rfl
      rfl (by rw [p36]; exact hdom _ _ h36)
  have hacc : b.written.fpAccess = true := Sys.fpAccess_of_cpacr hcp
  let wf : Sys := { b.written with fpcr := fpcrValue }
  let b37 : Boot := { b36 with core := { b36.core with pc := b36.core.pc + 4 }, written := wf }
  have p37 : b37.core.pc = after a 37 := by
    show b36.core.pc + 4 = _
    rw [p36, ← after_succ]
  have s36 : BootStep h R code b36 b37 := by
    have := boot_msrOf (h := h) (R := R) (b := b36) (r := .fpcr) (t := 1) (w := wf)
      (by rw [p36]; exact h36) hsp off33
      (show (!(b.written.fpAccess && b.written.fpAccess)) = false by simp [hacc])
      (show some { b.written with fpcr := (b35.core.setX 1 v).x 1 } = some wf by
        rw [State.x_setX_same (r := 1) (by decide), ev] <;> rfl)
    rw [show keepsTlb .fpcr b36.written wf = true from rfl] at this
    exact this
  have off37 : b37.mmuOff := off33
  have hn41 : (after a 41).toNat < 2 ^ 55 := by
    have e : after a 42 = after a 41 + 4 := after_succ a 41
    rw [UInt64.le_iff_toNat_le, e, UInt64.toNat_add] at ha
    rw [UInt64.lt_iff_toNat_lt, e, UInt64.toNat_add] at ha'
    have := (after a 41).toNat_lt
    simp only [UInt64.reduceToNat, Nat.reducePow] at ha ha' this ⊢
    omega
  obtain ⟨c, rc, pc, xc, -, sc, mc, oc⟩ :=
    boot_movImm (h := h) (R := R) (b := b37) hdom (by decide) h37 p37 hsp off37
      (by rw [after_after]; exact hn41)
  rw [after_after] at pc
  let ws : Sys := { b.written with sctlr := sctlrOn, fpcr := fpcrValue }
  let b42 : Boot := { b37 with core := { c with pc := c.pc + 4 }, written := ws }
  have p42 : b42.core.pc = after a 42 := by
    show c.pc + 4 = _
    rw [pc, ← after_succ]
  have hk : keepsTlb .sctlr wf ws = true := by
    show (b.written.sctlr ||| 1 == sctlrOn ||| 1) = true
    rw [hw]
    decide
  have s41 : BootStep h R code { b37 with core := c } b42 := by
    have := boot_msrOf (h := h) (R := R) (b := { b37 with core := c }) (r := .sctlr) (t := 1)
      (w := ws) (by rw [pc]; exact h41) hsp off37 rfl (by rw [xc]; rfl)
    rw [hk] at this
    exact this
  have hmem : c.mem = b.core.mem := mc.trans (State.setX_mem (s := b35.core) (r := 1) (v := v))
  have hf : fetchOk h b42.written b42.tlb b42.core.mem b42.core.pc :=
    .inr ⟨rfl, true, classify_normal hcov
      (fun j hj => (congrFun (hmem.trans hm) _).trans (htab j hj))
      (by rw [p42]; exact ha) (by rw [p42]; exact ha')⟩
  have s42 : BootStep h R code b42
      { b42 with core := { b42.core with pc := b42.core.pc + 4 }, eff := b42.written } :=
    .sys (i := .isb) (by rw [p42]; exact h42) (decode_encode _) (.inl hsp) (.inl hoff.2) hf rfl
  refine ⟨_, hb.trans (.next s32 (.next s33 (.next s34 (.next s35 (.next s36
      (rc.trans (.next s41 (.single s42)))))))),
    ?_, hsp, rfl, rfl, rfl, hmem.trans hm, ?_, ?_, rfl⟩
  · show c.pc + 4 + 4 = _
    rw [pc, ← after_succ, ← after_succ]
  · show c.sp = _
    rw [sc]
    exact (State.setX_sp (s := b35.core) (r := 1) (v := v)).trans hs
  · show c.out = _
    rw [oc]
    exact (State.setX_out (s := b35.core) (r := 1) (v := v)).trans hout

/-- The run of an image's entry and of the startup's instructions 0 to 42 in the boot model, for
an image at a multiple of 4096 in the RAM GiB.  From the entry with the MMU off and the image's
translation table in memory, the machine selects SP_EL1, branches to the startup, finds itself at
EL1, enables floating point, writes `FPCR`, and turns the MMU on, whether or not the processor has
`TCR2_EL1`.  It ends with the written system registers in effect in the covered configuration, the
table at `TTBR0_EL1`, clean TLBs, and every store to the UART complete, and it changes no byte of
memory, SP, or the UART's output. -/
theorem boot_startupOff (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) {image : UInt64}
    {n : Nat} {m : Module} {cap : Nat} {room : UInt64}
    {is : List Instr} {b : Boot} (himg : image.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ image.toNat)
    (hhi : image.toNat + (layoutOf image n m cap room).size ≤ 0x80000000)
    (hs : startupCode (layoutOf image n m cap room) = .ok is)
    (hhead : CodeAt code image [.spsel1, .b 15]) (hcode : CodeAt code (image + 64) is)
    (hpc : b.core.pc = image) (hoff : b.mmuOff)
    (htab : ∀ j (hj : j < 32),
      b.core.mem ((layoutOf image n m cap room).table + UInt64.ofNat j) = tableBytes[j]) :
    ∃ b', BootReach h R code b b' ∧ b'.core.pc = after (image + 64) 43 ∧ b'.spSel = true ∧
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
  have h232 : (after (image + 64) 42).toNat = image.toNat + 232 := by
    rw [after, UInt64.add_assoc, show (64 : UInt64) + 4 * UInt64.ofNat 42 = 232 by decide,
      UInt64.toNat_add]
    show (image.toNat + 232) % 2 ^ 64 = _
    omega
  have ha42 : 0x40000000 ≤ after (image + 64) 42 := by
    rw [UInt64.le_iff_toNat_le, h232]
    show 1073741824 ≤ _
    omega
  have ha42' : after (image + 64) 42 < 0x80000000 := by
    rw [UInt64.lt_iff_toNat_lt, h232]
    show _ < 2147483648
    unfold tabOff at hao
    omega
  have hlt : ∀ k, k ≤ 43 → (after (image + 64) k).toNat < 2 ^ 55 := by
    intro k hk
    simp only [after, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
      UInt64.reduceToNat, Nat.reducePow]
    omega
  generalize hL : layoutOf image n m cap room = L at hs htab hT32 hTlt ⊢
  have hLi : L.image = image := by
    subst hL
    rfl
  obtain ⟨_, skip, vec, tab, _, _, _, _, _, _, -, hskip, hvec, htc, -, -, -, -, -, -, his⟩ :=
    startupCode_ok hs
  rw [hLi] at hskip hvec htc
  rw [his] at hcode
  generalize hs0 : image + 64 = s at hcode hskip hvec htc ha42 ha42' hlt ⊢
  iterate 11 replace hcode := ((CodeAt.append (code := code)).mp hcode).1
  have hm4 : ∀ d v, (movImm d v).length = 4 := fun _ _ => rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append, CodeAt.append, CodeAt.cons,
    after_after, addrOf_length hvec, addrOf_length htc, hm4, Nat.reduceAdd] at hcode
  obtain ⟨c0, c1, c2, c3, cv, c6, cm7, c11, c12, c13, cm14, c18, cm19, c23, ct, c26, c27, c28,
    c29, c30, c31, c32, c33, c34, c35, c36, cm37, c41, c42, -⟩ := hcode
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
        (congrArg (fun p : UInt64 => some ({ b.core with pc := p } : State)) e64)
        (by rw [← after_zero s]; exact hlt 0 (by decide)))),
      (after_zero s).symm, rfl, hoff, rfl, rfl, rfl, rfl⟩
  rw [← after_zero s] at c0
  have hS : sctlrOn - 1 &&& 1 = 0 := by decide
  have e48 : UInt64.ofNat (0x30 : Fin 65536).val <<< UInt64.ofNat (16 * (1 : Fin 4).val) =
      cpacrValue := by decide
  obtain ⟨b2, r2, o2, x2⟩ := OffAt.mrs r1 o1 (by decide) c0 rfl
  obtain ⟨d3, q3, p3, sp3, m3, out3⟩ := run_checkEL (P := noMemory) c1 c2 c3 o2.pc x2
  obtain ⟨d5, q5, p5, x5, -, sp5, m5, out5⟩ := run_addrOf noMemory code hvec (by decide) cv p3
  obtain ⟨r5, o5⟩ := OffAt.core r2 o2
    (bootReach_of_reach_off hdom o2.spSel o2.off (q3.trans q5) (out5.trans out3)
      (by rw [p5.trans (after_after _ _ _)]; exact hlt _ (by decide)))
    (p5.trans (after_after _ _ _)) (m5.trans m3) (sp5.trans sp3) (out5.trans out3)
  obtain ⟨b6, r6, o6⟩ := OffAt.msr r5 o5 c6 (w' := { b.written with vbar := L.vectors }) rfl
    (by rw [x5]; rfl) hoff.2
  obtain ⟨d10, q10, p10, x10, -, sp10, m10, out10⟩ :=
    boot_movImm (h := h) (R := R) hdom (by decide) cm7 o6.pc o6.spSel o6.off
      (by rw [after_after]; exact hlt _ (by decide))
  obtain ⟨r10, o10⟩ := OffAt.core r6 o6 q10 (p10.trans (after_after _ _ _)) m10 sp10 out10
  obtain ⟨b11, r11, o11⟩ := OffAt.msr r10 o10 c11
    (w' := { b.written with vbar := L.vectors, sctlr := sctlrOn - 1 }) rfl (by rw [x10]; rfl) hS
  obtain ⟨b12, r12, o12, x12⟩ := OffAt.movz r11 o11 (by decide) c12 (hlt _ (by decide))
  obtain ⟨b13, r13, o13⟩ := OffAt.msr r12 o12 c13
    (w' := { b.written with vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := cpacrValue }) rfl
    (by rw [x12, e48]; rfl) hS
  obtain ⟨d17, q17, p17, x17, -, sp17, m17, out17⟩ :=
    boot_movImm (h := h) (R := R) hdom (by decide) cm14 o13.pc o13.spSel o13.off
      (by rw [after_after]; exact hlt _ (by decide))
  obtain ⟨r17, o17⟩ := OffAt.core r13 o13 q17 (p17.trans (after_after _ _ _)) m17 sp17 out17
  obtain ⟨b18, r18, o18⟩ := OffAt.msr r17 o17 c18
    (w' := { b.written with
      vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := cpacrValue, mair := mairValue })
    rfl (by rw [x17]; rfl) hS
  obtain ⟨d22, q22, p22, x22, -, sp22, m22, out22⟩ :=
    boot_movImm (h := h) (R := R) hdom (by decide) cm19 o18.pc o18.spSel o18.off
      (by rw [after_after]; exact hlt _ (by decide))
  obtain ⟨r22, o22⟩ := OffAt.core r18 o18 q22 (p22.trans (after_after _ _ _)) m22 sp22 out22
  obtain ⟨b23, r23, o23⟩ := OffAt.msr r22 o22 c23
    (w' := { b.written with
      vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := cpacrValue, mair := mairValue,
      tcr := tcrValue })
    rfl (by rw [x22]; rfl) hS
  obtain ⟨d25, q25, p25, x25, -, sp25, m25, out25⟩ :=
    boot_addrOf (h := h) (R := R) hdom htc (by decide) ct o23.pc o23.spSel o23.off
      (by rw [after_after]; exact hlt _ (by decide))
  obtain ⟨r25, o25⟩ := OffAt.core r23 o23 q25 (p25.trans (after_after _ _ _)) m25 sp25 out25
  obtain ⟨b26, r26, o26⟩ := OffAt.msr r25 o25 c26
    (w' := { b.written with
      vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := cpacrValue, mair := mairValue,
      tcr := tcrValue, ttbr0 := L.table })
    rfl (by rw [x25]; rfl) hS
  obtain ⟨b27, r27, o27, x27⟩ := OffAt.mrs r26 o26 (by decide) c27 rfl
  obtain ⟨d30, q30, p30, sp30, m30, out30⟩ :=
    run_mmfr3 (P := noMemory) c28 c29 c30 hskip o27.pc
  rw [x27] at p30
  obtain ⟨r30, o30⟩ := OffAt.core r27 o27
    (bootReach_of_reach_off hdom o27.spSel o27.off q30 out30
      (by rw [p30]; split <;> exact hlt _ (by decide)))
    p30 m30 sp30 out30
  obtain ⟨w, b32, r32, o32, hw32, hcp32, hcov32, hT32'⟩ : ∃ w b32, BootReach h R code b b32 ∧
      OffAt b (after s 32) w b32 ∧ w.sctlr = sctlrOn - 1 ∧ w.cpacr = cpacrValue ∧
      { w with sctlr := sctlrOn, fpcr := fpcrValue }.covered h = true ∧ w.ttbr0 = L.table := by
    cases ht : h.tcrx
    · have hz : h.mmfr3 &&& 15 = 0 := by simpa [Hw.tcrx] using ht
      rw [ite_eq_left hz] at o30
      exact ⟨_, _, r30, o30, rfl, rfl, by simp [Sys.covered, Sys.fpOn, ht, hT32, hTlt], rfl⟩
    · have hz : ¬ h.mmfr3 &&& 15 = 0 := by simpa [Hw.tcrx] using ht
      rw [ite_eq_right hz] at o30
      obtain ⟨b31, r31, o31⟩ := OffAt.msr r30 o30 c31
        (w' := { b.written with
          vbar := L.vectors, sctlr := sctlrOn - 1, cpacr := cpacrValue, mair := mairValue,
          tcr := tcrValue, ttbr0 := L.table, tcr2 := 0 })
        rfl (by show (if h.tcrx then some _ else none) = _; exact (ite_eq_left ht).trans rfl)
        hS
      exact ⟨_, _, r31, o31, rfl, rfl, by simp [Sys.covered, Sys.fpOn, ht, hT32, hTlt], rfl⟩
  obtain ⟨bf, rf, pf, spf, wef, tlbf, eff, mf, sf, of, uf⟩ :=
    OffAt.mmuOn hdom r32 o32 c32 c33 c34 c35 c36 cm37 c41 c42 hw32 hcp32 hcov32
      (fun j hj => by rw [hT32']; exact htab j hj) ha42 ha42'
  exact ⟨bf, rf, pf, spf, wef, tlbf, by rw [eff]; exact hcov32, by rw [eff]; exact hT32', mf, sf,
    of, uf⟩

end LeanExe.A64
