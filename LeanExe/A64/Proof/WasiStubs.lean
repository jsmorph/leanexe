module

public import LeanExe.A64.Proof.Memory32
public import LeanExe.A64.Proof.StampStages
public import LeanExe.A64.Wasi

@[expose] public section

/-!
The runs of the parts of the stubs of `LeanExe/A64/Wasi.lean` in the program's model.
`run_bufferChecks` loads the iovec's pointer and length from the guest's bytes 0 to 7 of a store
that the area holds and reaches the trap stub when the buffer exceeds the memory or `2^32`.
`run_bufferCall` sets the arguments of the call, and `run_resultTail` stores a count, returns an
errno through `run_errnoRoutine`, or reaches the trap stub.  `run_neImm`, `run_loImm`, and
`run_hiImm` are the comparisons of a register with an immediate that the stubs' checks make.
The call itself, `BL` to the routine `SVC #0; RET` and back, is `run_callSvc`.
-/

namespace LeanExe.A64

open Wasm

/-! ## The generator's parts -/

theorem bufferChecks_ok {a tr : UInt64} {is : List Instr} (hg : bufferChecks a tr = .ok is) :
    ∃ g1 g2, cbField (after a 7) tr = .ok g1 ∧ cbField (after a 10) tr = .ok g2 ∧
      is = [.ldr 9 17 512, .orrW 10 31 9, .lsrImm 11 9 32, .addReg 12 10 11, .ldr 13 17 0,
        .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 g1, .movz 13 1 2, .subsReg 31 12 13,
        .bcond 8 g2] := by
  unfold bufferChecks at hg
  cases h1 : cbField (after a 7) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h2 : cbField (after a 10) tr with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g2 =>
  simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g2, rfl, rfl, hg.symm⟩

theorem bufferCall_ok {a svc : UInt64} {nr : Fin 65536} {is : List Instr}
    (hg : bufferCall a svc nr = .ok is) :
    ∃ g, bField (after a 6) svc = .ok g ∧
      is = [.addReg 1 17 10, .addImm 1 1 4095, .addImm 1 1 1, .orrReg 2 31 11, .movz 8 nr 0,
        .orrReg 19 31 30, .bl g] := by
  unfold bufferCall at hg
  cases h1 : bField (after a 6) svc with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g =>
  simp only [h1, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g, rfl, hg.symm⟩

theorem resultTail_ok {a tr en : UInt64} {is : List Instr} (hg : resultTail a tr en = .ok is) :
    ∃ g1 g2 g3, cbField (after a 1) (after a 12) = .ok g1 ∧ cbField (after a 14) tr = .ok g2 ∧
      bField (after a 16) en = .ok g3 ∧
      is = [.subsReg 31 0 11, .bcond 8 g1, .addImm 16 17 12, .strb 0 16 4092, .lsrImm 12 0 8,
        .strb 12 16 4093, .lsrImm 12 0 16, .strb 12 16 4094, .lsrImm 12 0 24, .strb 12 16 4095,
        .movz 0 0 0, .ret 19, .subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g2,
        .orrReg 0 31 12, .bl g3, .ret 19] := by
  unfold resultTail at hg
  cases h1 : cbField (after a 1) (after a 12) with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h2 : cbField (after a 14) tr with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g2 =>
  cases h3 : bField (after a 16) en with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok g3 =>
  simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g2, g3, rfl, rfl, rfl, hg.symm⟩

/-! ## Comparisons -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- `SUBS XZR, Xr, #imm` and `B.NE` to `tB`: the branch is taken unless X`r` holds `imm`. -/
theorem run_neImm {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288}
    (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 1 g])
    (hg : after a 1 + sext 19 g.val * 4 = tB) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x r = UInt64.ofNat imm.val then after a 2 else tB) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x r) (UInt64.ofNat imm.val) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsImm 31 r imm) s = some s1 := by
    simp only [exec, State.xsp_eq_x hr]
    rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 1 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 1 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_one]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 1 = !decide (s.x r = UInt64.ofNat imm.val) := by
    show (!(s.subs 31 (s.x r) (UInt64.ofNat imm.val)).zFlag) = _
    rw [subs_z]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 1 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : s.x r = UInt64.ofNat imm.val
    · rw [ite_eq_right (by simp [h]), ite_eq_left h, ← after_succ]
    · rw [ite_eq_left (by simpa using h), ite_eq_right h]
      exact hg
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).io = _
    exact State.setX_io

/-- `SUBS XZR, Xr, #imm` and `B.LO` to `tB`: the branch is taken when X`r` lies below `imm`. -/
theorem run_loImm {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288}
    (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 3 g])
    (hg : after a 1 + sext 19 g.val * 4 = tB) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x r < UInt64.ofNat imm.val then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x r) (UInt64.ofNat imm.val) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsImm 31 r imm) s = some s1 := by
    simp only [exec, State.xsp_eq_x hr]
    rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 3 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 3 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_one]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 3 = decide (s.x r < UInt64.ofNat imm.val) := by
    rw [condHolds_3]
    show (!decide (UInt64.ofNat imm.val ≤ s.x r)) = _
    by_cases h : s.x r < UInt64.ofNat imm.val
    · rw [decide_eq_true h, decide_eq_false (UInt64.not_le.mpr h)]
      rfl
    · rw [decide_eq_false h, decide_eq_true (UInt64.not_lt.mp h)]
      rfl
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 3 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : s.x r < UInt64.ofNat imm.val
    · rw [ite_eq_left (by simpa using h), ite_eq_left h]
      exact hg
    · rw [ite_eq_right (by simpa using h), ite_eq_right h, ← after_succ]
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).io = _
    exact State.setX_io

/-- `SUBS XZR, Xr, #imm` and `B.HI` to `tB`: the branch is taken when X`r` lies above `imm`. -/
theorem run_hiImm {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288}
    (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 8 g])
    (hg : after a 1 + sext 19 g.val * 4 = tB) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if UInt64.ofNat imm.val < s.x r then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x r) (UInt64.ofNat imm.val) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsImm 31 r imm) s = some s1 := by
    simp only [exec, State.xsp_eq_x hr]
    rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 8 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 8 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_one]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 8 = decide (UInt64.ofNat imm.val < s.x r) := by
    rw [condHolds_8]
    show (decide (UInt64.ofNat imm.val ≤ s.x r) && !(s.x r - UInt64.ofNat imm.val == 0)) = _
    exact cond_hi _ _
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 8 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : UInt64.ofNat imm.val < s.x r
    · rw [ite_eq_left (by simpa using h), ite_eq_left h]
      exact hg
    · rw [ite_eq_right (by simpa using h), ite_eq_right h, ← after_succ]
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).io = _
    exact State.setX_io

/-! ## Steps -/

/-- A step of `ADD Xd, Xn, Xm`. -/
theorem step_addReg {s : State} {d n m : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.addReg d n m))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n + s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `SUB Xd, Xn, Xm`. -/
theorem step_subReg {s : State} {d n m : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.subReg d n m))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n - s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `MADD Xd, Xn, Xm, Xa`. -/
theorem step_madd {s : State} {d n m r : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.madd d n m r))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x r + s.x n * s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `ORR Xd, XZR, Xm`, a move. -/
theorem step_mov {s : State} {d m : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.orrReg d 31 m))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨t, r, p, xd, xq, sp, mem, io⟩ := step_setX P code (v := s.x 31 ||| s.x m) hd hc rfl
  refine ⟨t, r, p, ?_, xq, sp, mem, io⟩
  rw [xd]
  show 0 ||| s.x m = s.x m
  exact UInt64.zero_or

/-- A step of `ADD Xd, Xn, #imm` with registers other than SP. -/
theorem step_addImm {s : State} {d n : Fin 32} {imm : Fin 4096} (hd : d.val < 31)
    (hn : n.val < 31) (hc : code s.pc = some (encode (.addImm d n imm))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n + UInt64.ofNat imm.val ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc (exec_addImm_x P hd hn)

/-- A step of `MOVZ Xd, #imm, LSL #(16 * hw)`. -/
theorem step_movz {s : State} {d : Fin 32} {imm : Fin 65536} {hw : Fin 4} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.movz d imm hw))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧
      t.x d = UInt64.ofNat imm.val <<< UInt64.ofNat (16 * hw.val) ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `LDR Xt, [Xn, #(8 * i)]` of Normal memory, with a base other than SP. -/
theorem step_ldr {s : State} {t n : Fin 32} {i : Nat} (hi : i < 4096) (ht : t.val < 31)
    (hn : n.val < 31) (hc : code s.pc = some (encode (.ldr t n ⟨i, hi⟩)))
    (hmap : ∀ k < 8, P.normal (s.x n + UInt64.ofNat (8 * i + k)) = true) :
    ∃ u, Reach P code s u ∧ u.pc = s.pc + 4 ∧
      u.x t = load64 s.mem (s.x n + UInt64.ofNat (8 * i)) ∧
      (∀ q : Fin 32, q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧ u.io = s.io :=
  step_setX P code ht hc (exec_ldr_base P hi hn hmap)

/-- A step of `ORR Wd, WZR, Wn`, which keeps the low 32 bits. -/
theorem step_orrW {s : State} {d n : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.orrW d 31 n))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = (s.x n).toUInt32.toUInt64 ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨t, r, p, xd, xq, sp, mem, io⟩ :=
    step_setX P code (v := (s.x 31 ||| s.x n).toUInt32.toUInt64) hd hc rfl
  refine ⟨t, r, p, ?_, xq, sp, mem, io⟩
  rw [xd]
  show (0 ||| s.x n).toUInt32.toUInt64 = _
  rw [UInt64.zero_or]

/-- A step of `RET Xn`. -/
theorem step_ret {s : State} {n : Fin 32} (hc : code s.pc = some (encode (.ret n))) :
    ∃ t, Reach P code s t ∧ t.pc = s.x n ∧ (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io :=
  ⟨_, reach_exec P code hc rfl (.refl _), rfl, fun _ => rfl, rfl, rfl, rfl⟩

/-- A step of `BL` to `target`, which sets X30 to the next word. -/
theorem step_bl {s : State} {g : Fin 67108864} {target : UInt64}
    (hc : code s.pc = some (encode (.bl g))) (hg : s.pc + sext 26 g.val * 4 = target) :
    ∃ t, Reach P code s t ∧ t.pc = target ∧ t.x 30 = s.pc + 4 ∧
      (∀ q : Fin 32, q ≠ 30 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  refine ⟨{ s.setX 30 (s.pc + 4) with pc := s.pc + sext 26 g.val * 4 },
    reach_exec P code hc rfl (.refl _), hg, ?_, fun q hq => ?_, State.setX_sp, State.setX_mem,
    State.setX_io⟩
  · rw [State.x_withPc, State.x_setX_same (by decide)]
  · rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]

/-- A step of `B` to `target`. -/
theorem step_b {s : State} {g : Fin 67108864} {target : UInt64}
    (hc : code s.pc = some (encode (.b g))) (hg : s.pc + sext 26 g.val * 4 = target) :
    ∃ t, Reach P code s t ∧ t.pc = target ∧ (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io :=
  ⟨{ s with pc := s.pc + sext 26 g.val * 4 }, reach_exec P code hc rfl (.refl _), hg,
    fun _ => rfl, rfl, rfl, rfl⟩

/-- A step of `CBZ Xr` or `CBNZ Xr` to `target`. -/
theorem step_cbz {s : State} {r : Fin 32} {g : Fin 524288} {target : UInt64}
    (hc : code s.pc = some (encode (.cbz r g))) (hg : s.pc + sext 19 g.val * 4 = target) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x r = 0 then target else s.pc + 4) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  refine ⟨{ s with pc := if s.x r = 0 then s.pc + sext 19 g.val * 4 else s.pc + 4 },
    reach_exec P code hc rfl (.refl _), ?_, fun _ => rfl, rfl, rfl, rfl⟩
  show (if s.x r = 0 then s.pc + sext 19 g.val * 4 else s.pc + 4) = _
  rw [hg]

theorem step_cbnz {s : State} {r : Fin 32} {g : Fin 524288} {target : UInt64}
    (hc : code s.pc = some (encode (.cbnz r g))) (hg : s.pc + sext 19 g.val * 4 = target) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x r ≠ 0 then target else s.pc + 4) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  refine ⟨{ s with pc := if s.x r ≠ 0 then s.pc + sext 19 g.val * 4 else s.pc + 4 },
    reach_exec P code hc rfl (.refl _), ?_, fun _ => rfl, rfl, rfl, rfl⟩
  show (if s.x r ≠ 0 then s.pc + sext 19 g.val * 4 else s.pc + 4) = _
  rw [hg]

/-! ## The routine of errnos -/

/-- The errno that the entries `l` of a table give the number `v`, and 29 for a number that no
entry names. -/
def errnoLookup : List (Fin 4096 × Fin 65536) → UInt64 → UInt64
  | [], _ => 29
  | x :: rest, v => if v = UInt64.ofNat x.1.val then UInt64.ofNat x.2.val else errnoLookup rest v

/-- The code of the routine of errnos for the entries `l`. -/
def errnoCode (l : List (Fin 4096 × Fin 65536)) : List Instr :=
  l.flatMap (fun x => [.subsImm 31 0 x.1, .bcond 1 3, .movz 0 x.2 0, .ret 30]) ++
    [.movz 0 29 0, .ret 30]

theorem errnoRoutine_eq : errnoRoutine = errnoCode errnoTable := rfl

theorem sext_three : sext 19 3 * 4 = 12 := by decide

theorem after_add (a : UInt64) (m k : Nat) :
    after a m + UInt64.ofNat (4 * k) = after a (m + k) := by
  simp only [after, UInt64.ofNat_add, UInt64.mul_add, UInt64.add_assoc]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

theorem movz0_val (v : Fin 65536) :
    UInt64.ofNat v.val <<< UInt64.ofNat (16 * (0 : Fin 4).val) = UInt64.ofNat v.val := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Fin.val_zero, Nat.mul_zero,
    Nat.zero_mod, Nat.shiftLeft_zero, Nat.mod_mod]

/-- The run of the routine of errnos for the entries `l` from its entry at `a`: the return to X30
with the errno of the number in X0 in X0, and every other register, SP, the memory, and the UART's
state kept. -/
theorem run_errnoCode : ∀ (l : List (Fin 4096 × Fin 65536)) {a : UInt64} {s : State},
    CodeAt code a (errnoCode l) → s.pc = a →
    ∃ t, Reach P code s t ∧ t.pc = s.x 30 ∧ t.x 0 = errnoLookup l (s.x 0) ∧
      (∀ q : Fin 32, q ≠ 0 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io
  | [], a, s, hcode, hpc => by
      have c0 := hcode 0 (by simp [errnoCode])
      have c1 := hcode 1 (by simp [errnoCode])
      simp only [errnoCode, List.flatMap_nil, List.nil_append, List.getElem_cons_zero,
        List.getElem_cons_succ, after_zero] at c0 c1
      obtain ⟨t1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_movz P code (s := s) (d := 0) (imm := 29)
        (hw := 0) (by decide) (by rw [hpc]; exact c0)
      obtain ⟨t2, r2, p2, k2, sp2, m2, io2⟩ := step_ret P code (s := t1) (n := 30)
        (by rw [p1, hpc, ← after_one]; exact c1)
      refine ⟨t2, r1.trans r2, by rw [p2, k1 30 (by decide)], ?_, fun q hq => by
        rw [k2, k1 q hq], by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩
      rw [k2, x1, movz0_val]
      show UInt64.ofNat (29 : Fin 65536).val = 29
      decide
  | x :: rest, a, s, hcode, hpc => by
      have hsplit : errnoCode (x :: rest) =
          [.subsImm 31 0 x.1, .bcond 1 3, .movz 0 x.2 0, .ret 30] ++ errnoCode rest := by
        simp [errnoCode]
      rw [hsplit] at hcode
      have hc := (CodeAt.append (code := code)).mp hcode
      have c2 := CodeAt.split code hc.1 (l1 := [.subsImm 31 0 x.1, .bcond 1 3]) rfl
      obtain ⟨t1, r1, p1, x1, sp1, m1, io1⟩ := run_neImm P code (tB := after a 4) (by decide)
        c2.1 (by
          show after a 1 + sext 19 3 * 4 = after a 4
          rw [sext_three, show (12 : UInt64) = UInt64.ofNat (4 * 3) from rfl, after_add]) hpc
      by_cases hx : s.x 0 = UInt64.ofNat x.1.val
      · rw [ite_eq_left hx] at p1
        have c3 := c2.2 0 (by simp)
        have c4 := c2.2 1 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c3 c4
        obtain ⟨t2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_movz P code (s := t1) (d := 0)
          (imm := x.2) (hw := 0) (by decide) (by rw [p1]; exact c3)
        obtain ⟨t3, r3, p3, k3, sp3, m3, io3⟩ := step_ret P code (s := t2) (n := 30)
          (by rw [p2, p1, ← after_succ]; exact c4)
        refine ⟨t3, r1.trans (r2.trans r3), by rw [p3, k2 30 (by decide), x1], ?_,
          fun q hq => by rw [k3, k2 q hq, x1], by rw [sp3, sp2, sp1], by rw [m3, m2, m1],
          by rw [io3, io2, io1]⟩
        rw [k3, x2, movz0_val]
        simp only [errnoLookup, hx, ↓reduceIte]
      · rw [ite_eq_right hx] at p1
        obtain ⟨t2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_errnoCode rest (s := t1) hc.2 p1
        refine ⟨t2, r1.trans r2, by rw [p2, x1], ?_, fun q hq => by rw [k2 q hq, x1],
          by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩
        rw [x2, x1]
        simp only [errnoLookup, hx, ↓reduceIte]

/-- The run of `errnoRoutine` from its entry. -/
theorem run_errnoRoutine {en : UInt64} (hen : CodeAt code en errnoRoutine) {s : State}
    (hpc : s.pc = en) :
    ∃ t, Reach P code s t ∧ t.pc = s.x 30 ∧ t.x 0 = errnoLookup errnoTable (s.x 0) ∧
      (∀ q : Fin 32, q ≠ 0 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  run_errnoCode P code errnoTable hen hpc

/-! ## The buffer's checks and the call -/

/-- The low half of the word of eight bytes whose lower four hold Talos's memory from `x` is
Talos's `read32` at `x`. -/
theorem load64_low32 {mem : UInt64 → UInt8} {b : UInt64} {m : Mem} {x : UInt32}
    (h0 : mem b = m.bytes x.toNat) (h1 : mem (b + 1) = m.bytes (x.toNat + 1))
    (h2 : mem (b + 2) = m.bytes (x.toNat + 2)) (h3 : mem (b + 3) = m.bytes (x.toNat + 3)) :
    (load64 mem b).toUInt32.toUInt64 = (m.read32 x).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, load64_toNat, UInt32.toNat_toUInt64,
    read32_toNat, h0, h1, h2, h3]
  have := byte_lt (mem (b + 4))
  have := byte_lt (mem (b + 5))
  have := byte_lt (mem (b + 6))
  have := byte_lt (mem (b + 7))
  have := byte_lt (m.bytes x.toNat)
  have := byte_lt (m.bytes (x.toNat + 1))
  have := byte_lt (m.bytes (x.toNat + 2))
  have := byte_lt (m.bytes (x.toNat + 3))
  simp only [Nat.reducePow] at *
  omega

/-- Byte `k` above X17 + 4096 holds byte `k` of the memory of a store that the area holds. -/
theorem StoreRel.byte {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {s : State}
    (h : StoreRel P cap gts st s) {k : Nat} (hk : k < cap * 65536) :
    s.mem (s.x 17 + UInt64.ofNat 4096 + UInt64.ofNat k) = st.mem.bytes k := by
  rw [add_ofNat_add]
  exact h.bytes k hk

/-- The checks of the buffer of the iovec at guest address 0, from `a`, on a machine that holds a
store in the area at X17: at the checks' end, the pointer in X10 and the length in X11 when the
buffer lies within the memory and below `2^32`, and the trap stub `tr` otherwise.  X9 to X13 and
the flags change. -/
theorem run_bufferChecks {a tr : UInt64} {g1 g2 : Fin 524288}
    (hcode : CodeAt code a [.ldr 9 17 512, .orrW 10 31 9, .lsrImm 11 9 32, .addReg 12 10 11,
      .ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 g1, .movz 13 1 2,
      .subsReg 31 12 13, .bcond 8 g2])
    (hg1 : cbField (after a 7) tr = .ok g1) (hg2 : cbField (after a 10) tr = .ok g2)
    {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {s : State}
    (hsr : StoreRel P cap gts st s) (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → t.x q = s.x q) ∧
      if (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ st.mem.pages * 65536 ∧
          (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ 2 ^ 32 then
        t.pc = after a 11 ∧ t.x 10 = (st.mem.read32 0).toUInt64 ∧
          t.x 11 = (st.mem.read32 4).toUInt64
      else t.pc = tr := by
  have c := fun k (hk : k < 11) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have c4 := c 4 (by omega)
  have c5 := c 5 (by omega)
  have c8 := c 8 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5 c8
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  have hca : 4096 + 65536 ≤ areaSize cap := by unfold areaSize; omega
  obtain ⟨u1, r1, p1, x9, k1, sp1, m1, io1⟩ := step_ldr P code (s := s) (t := 9) (n := 17)
    (i := 512) (by decide) (by decide) (by decide) (by rw [hpc]; exact c0)
    (fun k hk => hsr.mapped _ (by omega))
  have hb : ∀ j < 8, s.mem (s.x 17 + UInt64.ofNat (8 * 512) + UInt64.ofNat j) =
      st.mem.bytes j := fun j hj => by
    rw [add_ofNat_add]
    exact hsr.bytes j (by omega)
  have hptr : (u1.x 9).toUInt32.toUInt64 = (st.mem.read32 0).toUInt64 := by
    rw [x9]
    exact load64_low32 (by simpa using hb 0 (by omega)) (hb 1 (by omega)) (hb 2 (by omega))
      (hb 3 (by omega))
  have hlen : u1.x 9 >>> UInt64.ofNat 32 = (st.mem.read32 4).toUInt64 := by
    rw [x9]
    exact load64_shr32 (hb 4 (by omega)) (hb 5 (by omega)) (hb 6 (by omega)) (hb 7 (by omega))
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x10, k2, sp2, m2, io2⟩ := step_orrW P code (s := u1) (d := 10) (n := 9)
    (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x11, k3, sp3, m3, io3⟩ := step_lsrImm P code (s := u2) (d := 11) (n := 9)
    (k := 32) (by decide) (by rw [q2]; exact c2) (by decide)
  have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x12, k4, sp4, m4, io4⟩ := step_addReg P code (s := u3) (d := 12) (n := 10)
    (m := 11) (by decide) (by rw [q3]; exact c3)
  have q4 : u4.pc = after a 4 := by rw [p4, q3, ← after_succ]
  obtain ⟨u5, r5, p5, x13, k5, sp5, m5, io5⟩ := step_ldr P code (s := u4) (t := 13) (n := 17)
    (i := 0) (by decide) (by decide) (by decide) (by rw [q4]; exact c4)
    (fun k hk => by
      rw [k4 17 (by decide), k3 17 (by decide), k2 17 (by decide), k1 17 (by decide)]
      exact hsr.mapped _ (by omega))
  have q5 : u5.pc = after a 5 := by rw [p5, q4, ← after_succ]
  obtain ⟨u6, r6, p6, x13', k6, sp6, m6, io6⟩ := step_addImm P code (s := u5) (d := 13) (n := 13)
    (imm := 8) (by decide) (by decide) (by rw [q5]; exact c5)
  have q6 : u6.pc = after a 6 := by rw [p6, q5, ← after_succ]
  have hP : (st.mem.read32 0).toNat < 2 ^ 32 := (st.mem.read32 0).toNat_lt
  have hL : (st.mem.read32 4).toNat < 2 ^ 32 := (st.mem.read32 4).toNat_lt
  have h12 : u6.x 12 = (st.mem.read32 0).toUInt64 + (st.mem.read32 4).toUInt64 := by
    rw [k6 12 (by decide), k5 12 (by decide), x12, k3 10 (by decide), x10, hptr, x11,
      k2 9 (by decide), hlen]
  have h12n : (u6.x 12).toNat = (st.mem.read32 0).toNat + (st.mem.read32 4).toNat := by
    rw [h12, UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    simp only [Nat.reducePow] at *
    omega
  have e8 : (8 : Fin 4096).val = 8 := by decide
  rw [e8] at x13'
  have h13 : (u6.x 13).toNat = st.mem.pages * 65536 := by
    rw [x13', x13, k4 17 (by decide), k3 17 (by decide), k2 17 (by decide), k1 17 (by decide),
      m4, m3, m2, m1, Nat.mul_zero, add_ofNat_zero, hsr.size, UInt64.toNat_add,
      UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  have hkeep6 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → u6.x q = s.x q :=
    fun q h9 h10 h11 h12 h13 => by rw [k6 q h13, k5 q h13, k4 q h12, k3 q h11, k2 q h10, k1 q h9]
  have hr6 : Reach P code s u6 := r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))
  have hsp6 : u6.sp = s.sp := by rw [sp6, sp5, sp4, sp3, sp2, sp1]
  have hm6 : u6.mem = s.mem := by rw [m6, m5, m4, m3, m2, m1]
  have hio6 : u6.io = s.io := by rw [io6, io5, io4, io3, io2, io1]
  have c67 : CodeAt code (after a 6) [.subsReg 31 12 13, .bcond 8 g1] := by
    simpa using CodeAt.drop_take code hcode 6 2 (by simp)
  have c910 : CodeAt code (after a 9) [.subsReg 31 12 13, .bcond 8 g2] := by
    simpa using CodeAt.drop_take code hcode 9 2 (by simp)
  obtain ⟨u8, r8, p8, k8, sp8, m8, io8⟩ := run_hiReg P code (x := 12) (y := 13) (tB := tr)
    c67 (by rw [after_after]; exact hg1) q6
  by_cases hsize : (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ st.mem.pages * 65536
  · have hnlt : ¬ u6.x 13 < u6.x 12 := by
      rw [UInt64.lt_iff_toNat_lt, h12n, h13]
      omega
    rw [ite_eq_right hnlt, after_after] at p8
    obtain ⟨u9, r9, p9, x13'', k9, sp9, m9, io9⟩ := step_movz P code (s := u8) (d := 13)
      (imm := 1) (hw := 2) (by decide) (by rw [p8]; exact c8)
    have e32 : UInt64.ofNat (1 : Fin 65536).val <<< UInt64.ofNat (16 * (2 : Fin 4).val) =
        4294967296 := by decide
    rw [e32] at x13''
    have q9 : u9.pc = after a 9 := by rw [p9, p8, ← after_succ]
    obtain ⟨u11, r11, p11, k11, sp11, m11, io11⟩ := run_hiReg P code (x := 12) (y := 13)
      (tB := tr) c910 (by rw [after_after]; exact hg2) q9
    have h12' : u9.x 12 = u6.x 12 := by rw [k9 12 (by decide), k8]
    have hkeep9 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → u11.x q = s.x q :=
      fun q h9 h10 h11 h12 h13 => by rw [k11, k9 q h13, k8, hkeep6 q h9 h10 h11 h12 h13]
    refine ⟨u11, hr6.trans (r8.trans (r9.trans r11)), by rw [sp11, sp9, sp8, hsp6],
      by rw [m11, m9, m8, hm6], by rw [io11, io9, io8, hio6], hkeep9, ?_⟩
    by_cases h32 : (st.mem.read32 0).toNat + (st.mem.read32 4).toNat ≤ 2 ^ 32
    · have hnlt' : ¬ u9.x 13 < u9.x 12 := by
        rw [UInt64.lt_iff_toNat_lt, h12', h12n, x13'']
        simp only [UInt64.reduceToNat, Nat.reducePow] at *
        omega
      rw [ite_eq_right hnlt', after_after] at p11
      rw [if_pos ⟨hsize, h32⟩]
      refine ⟨p11, ?_, ?_⟩
      · rw [k11, k9 10 (by decide), k8, k6 10 (by decide), k5 10 (by decide), k4 10 (by decide),
          k3 10 (by decide), x10, hptr]
      · rw [k11, k9 11 (by decide), k8, k6 11 (by decide), k5 11 (by decide), k4 11 (by decide),
          x11, k2 9 (by decide), hlen]
    · have hlt' : u9.x 13 < u9.x 12 := by
        rw [UInt64.lt_iff_toNat_lt, h12', h12n, x13'']
        simp only [UInt64.reduceToNat, Nat.reducePow] at *
        omega
      rw [ite_eq_left hlt'] at p11
      rw [if_neg (fun h => h32 h.2)]
      exact p11
  · have hlt : u6.x 13 < u6.x 12 := by
      rw [UInt64.lt_iff_toNat_lt, h12n, h13]
      omega
    rw [ite_eq_left hlt] at p8
    refine ⟨u8, hr6.trans r8, by rw [sp8, hsp6], by rw [m8, hm6], by rw [io8, hio6],
      fun q h9 h10 h11 h12 h13 => by rw [k8, hkeep6 q h9 h10 h11 h12 h13], ?_⟩
    rw [if_neg (fun h => hsize h.1)]
    exact p8

/-- The arguments of a call of the buffer, from `a`: X1 at the buffer's address
`X17 + 4096 + X10`, X2 at the length in X11, X8 at the call's number `nr`, and X19 at the return
address in X30, before the `BL` at `after a 6`. -/
theorem run_bufferCall {a : UInt64} {nr : Fin 65536} {g : Fin 67108864}
    (hcode : CodeAt code a [.addReg 1 17 10, .addImm 1 1 4095, .addImm 1 1 1, .orrReg 2 31 11,
      .movz 8 nr 0, .orrReg 19 31 30, .bl g])
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = after a 6 ∧ t.x 1 = s.x 17 + UInt64.ofNat 4096 + s.x 10 ∧
      t.x 2 = s.x 11 ∧ t.x 8 = UInt64.ofNat nr.val ∧ t.x 19 = s.x 30 ∧
      (∀ q : Fin 32, q ≠ 1 → q ≠ 2 → q ≠ 8 → q ≠ 19 → t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io := by
  have c := fun k (hk : k < 7) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have c4 := c 4 (by omega)
  have c5 := c 5 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 1) (n := 17)
    (m := 10) (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 1) (n := 1)
    (imm := 4095) (by decide) (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addImm P code (s := u2) (d := 1) (n := 1)
    (imm := 1) (by decide) (by decide) (by rw [q2]; exact c2)
  have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_mov P code (s := u3) (d := 2) (m := 11)
    (by decide) (by rw [q3]; exact c3)
  have q4 : u4.pc = after a 4 := by rw [p4, q3, ← after_succ]
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_movz P code (s := u4) (d := 8) (imm := nr)
    (hw := 0) (by decide) (by rw [q4]; exact c4)
  have q5 : u5.pc = after a 5 := by rw [p5, q4, ← after_succ]
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_mov P code (s := u5) (d := 19) (m := 30)
    (by decide) (by rw [q5]; exact c5)
  have e1 : (4095 : Fin 4096).val = 4095 := by decide
  have e2 : (1 : Fin 4096).val = 1 := by decide
  rw [e1] at x2
  rw [e2] at x3
  refine ⟨u6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))), by
      rw [p6, q5, ← after_succ], ?_, ?_, ?_, ?_, ?_, by rw [sp6, sp5, sp4, sp3, sp2, sp1],
    by rw [m6, m5, m4, m3, m2, m1], by rw [io6, io5, io4, io3, io2, io1]⟩
  · rw [k6 1 (by decide), k5 1 (by decide), k4 1 (by decide), x3, x2, x1]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
    omega
  · rw [k6 2 (by decide), k5 2 (by decide), x4, k3 11 (by decide), k2 11 (by decide),
      k1 11 (by decide)]
  · rw [k6 8 (by decide), x5, movz0_val]
  · rw [x6, k5 30 (by decide), k4 30 (by decide), k3 30 (by decide), k2 30 (by decide),
      k1 30 (by decide)]
  · intro q h1 h2 h8 h19
    rw [k6 q h19, k5 q h8, k4 q h2, k3 q h1, k2 q h1, k1 q h1]

/-! ## The result -/

/-- The handling of a call's result in X0, from `a`, with the length in X11, the return address in
X19, the trap stub at `tr`, and the routine of errnos at `en`.  A result at most the length is
stored at guest address 8, the bytes 4104 to 4107 above X17, and errno 0 returned.  When the
negation of a result above the length is at most 4095, it is an error number, whose errno is
returned.  Any other result reaches the trap stub.  X17, X18, SP, and the UART's state keep their
values, and only the store of a count changes the memory. -/
theorem run_resultTail {a tr en : UInt64} {g1 g2 : Fin 524288} {g3 : Fin 67108864}
    (hcode : CodeAt code a [.subsReg 31 0 11, .bcond 8 g1, .addImm 16 17 12, .strb 0 16 4092,
      .lsrImm 12 0 8, .strb 12 16 4093, .lsrImm 12 0 16, .strb 12 16 4094, .lsrImm 12 0 24,
      .strb 12 16 4095, .movz 0 0 0, .ret 19, .subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g2,
      .orrReg 0 31 12, .bl g3, .ret 19])
    (hg1 : cbField (after a 1) (after a 12) = .ok g1) (hg2 : cbField (after a 14) tr = .ok g2)
    (hg3 : bField (after a 16) en = .ok g3) (hen : CodeAt code en errnoRoutine)
    {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 4, P.normal (s.x 17 + UInt64.ofNat (4104 + k)) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      ((s.x 0 ≤ s.x 11 ∧ t.pc = s.x 19 ∧ t.x 0 = 0 ∧
          t.mem = writeList s.mem (s.x 17 + UInt64.ofNat 4104)
            [(s.x 0).toUInt8, (s.x 0 >>> UInt64.ofNat 8).toUInt8,
              (s.x 0 >>> UInt64.ofNat 16).toUInt8, (s.x 0 >>> UInt64.ofNat 24).toUInt8]) ∨
        (s.x 11 < s.x 0 ∧ 0 - s.x 0 ≤ 4095 ∧ t.pc = s.x 19 ∧
          t.x 0 = errnoLookup errnoTable (0 - s.x 0) ∧ t.mem = s.mem) ∨
        (s.x 11 < s.x 0 ∧ 4095 < 0 - s.x 0 ∧ t.pc = tr ∧ t.mem = s.mem)) := by
  have c := fun k (hk : k < 18) => hcode k (by simpa using hk)
  have c2 := c 2 (by omega)
  have c10 := c 10 (by omega)
  have c11 := c 11 (by omega)
  have c12 := c 12 (by omega)
  have c15 := c 15 (by omega)
  have c16 := c 16 (by omega)
  have c17 := c 17 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c2 c10 c11 c12 c15 c16 c17
  have c01 : CodeAt code a [.subsReg 31 0 11, .bcond 8 g1] :=
    (CodeAt.split code (l1 := [.subsReg 31 0 11, .bcond 8 g1]) hcode rfl).1
  have cstr : CodeAt code (after a 3) [.strb 0 16 4092, .lsrImm 12 0 8, .strb 12 16 4093,
      .lsrImm 12 0 16, .strb 12 16 4094, .lsrImm 12 0 24, .strb 12 16 4095] := by
    simpa using CodeAt.drop_take code hcode 3 7 (by simp)
  have c1314 : CodeAt code (after a 13) [.subsImm 31 12 4095, .bcond 8 g2] := by
    simpa using CodeAt.drop_take code hcode 13 2 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiReg P code (x := 0) (y := 11)
    (tB := after a 12) c01 hg1 hpc
  by_cases hle : s.x 11 < s.x 0
  · rw [ite_eq_left hle] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_subReg P code (s := u1) (d := 12) (n := 31)
      (m := 0) (by decide) (by rw [p1]; exact c12)
    have hx2 : u2.x 12 = 0 - s.x 0 := by rw [x2, k1, k1]; rfl
    have q2 : u2.pc = after a 13 := by rw [p2, p1, ← after_succ]
    obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_hiImm P code (r := 12) (imm := 4095) (tB := tr)
      (by decide) c1314 (by rw [after_after]; exact cbField_target hg2) q2
    have e4095 : UInt64.ofNat (4095 : Fin 4096).val = 4095 := by decide
    rw [e4095, hx2] at p3
    have hkeep3 : ∀ q : Fin 32, q ≠ 12 → u3.x q = s.x q := fun q hq => by
      rw [k3, k2 q hq, k1]
    by_cases hbig : 4095 < 0 - s.x 0
    · rw [ite_eq_left hbig] at p3
      exact ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1],
        hkeep3 17 (by decide), hkeep3 18 (by decide),
        .inr (.inr ⟨hle, hbig, p3, by rw [m3, m2, m1]⟩)⟩
    · rw [ite_eq_right hbig, after_after] at p3
      obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_mov P code (s := u3) (d := 0) (m := 12)
        (by decide) (by rw [p3]; exact c15)
      have q4 : u4.pc = after a 16 := by rw [p4, p3, ← after_succ]
      obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_bl P code (s := u4) (target := en)
        (by rw [q4]; exact c16) (by rw [q4]; exact bField_target hg3)
      obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := run_errnoRoutine P code hen p5
      have q6 : u6.pc = after a 17 := by rw [p6, x5, q4, ← after_succ]
      obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_ret P code (s := u6) (n := 19)
        (by rw [q6]; exact c17)
      have hkeep7 : ∀ q : Fin 32, q ≠ 0 → q ≠ 12 → q ≠ 30 → u7.x q = s.x q :=
        fun q h0 h12 h30 => by rw [k7, k6 q h0, k5 q h30, k4 q h0, hkeep3 q h12]
      refine ⟨u7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))),
        by rw [sp7, sp6, sp5, sp4, sp3, sp2, sp1], by rw [io7, io6, io5, io4, io3, io2, io1],
        hkeep7 17 (by decide) (by decide) (by decide),
        hkeep7 18 (by decide) (by decide) (by decide),
        .inr (.inl ⟨hle, UInt64.not_lt.mp hbig, ?_, ?_, by rw [m7, m6, m5, m4, m3, m2, m1]⟩)⟩
      · rw [p7, k6 19 (by decide), k5 19 (by decide), k4 19 (by decide),
          hkeep3 19 (by decide)]
      · rw [k7, x6, k5 0 (by decide), x4, k3, hx2]
  · rw [ite_eq_right hle] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 16) (n := 17)
      (imm := 12) (by decide) (by decide) (by rw [p1]; exact c2)
    have e12 : (12 : Fin 4096).val = 12 := by decide
    rw [e12, k1] at x2
    have q2 : u2.pc = after a 3 := by rw [p2, p1, ← after_succ]
    have hB : ∀ k, u2.x 16 + UInt64.ofNat (4092 + k) = s.x 17 + UInt64.ofNat (4104 + k) := by
      intro k
      rw [x2, add_ofNat_add]
      congr 2
      omega
    obtain ⟨u3, r3, p3, sp3, io3, k3, m3⟩ := run_strb4 P code (v := 0) (t := 12) (s := u2)
      (by decide) (by decide) (by decide) cstr q2 (fun k hk => by rw [hB k]; exact hmap k hk) hU
    have q3 : u3.pc = after a 10 := by rw [p3, after_after]
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_movz P code (s := u3) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [q3]; exact c10)
    have q4 : u4.pc = after a 11 := by rw [p4, q3, ← after_succ]
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_ret P code (s := u4) (n := 19)
      (by rw [q4]; exact c11)
    have hkeep : ∀ q : Fin 32, q ≠ 0 → q ≠ 12 → q ≠ 16 → u5.x q = s.x q :=
      fun q h0 h12 h16 => by rw [k5, k4 q h0, k3 q h12, k2 q h16, k1]
    have hB0 : u2.x 16 + UInt64.ofNat 4092 = s.x 17 + UInt64.ofNat 4104 := by simpa using hB 0
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), by rw [sp5, sp4, sp3, sp2, sp1],
      by rw [io5, io4, io3, io2, io1], hkeep 17 (by decide) (by decide) (by decide),
      hkeep 18 (by decide) (by decide) (by decide),
      .inl ⟨UInt64.not_lt.mp hle, ?_, ?_, ?_⟩⟩
    · rw [p5, k4 19 (by decide), k3 19 (by decide), k2 19 (by decide), k1]
    · rw [k5, x4, movz0_val]
      decide
    · rw [m5, m4, m3, hB0, k2 0 (by decide), k1, m2, m1]

/-! ## The requests' checks -/

/-- The checks of an `fd_read` request, from `a`: descriptor 0, the iovec at 0, one iovec, and the
count at 8, or the trap stub. -/
theorem run_readHead {a tr : UInt64} {f0 f1 f3 f5 : Fin 524288}
    (hcode : CodeAt code a [.cbnz 0 f0, .cbnz 1 f1, .subsImm 31 2 1, .bcond 1 f3,
      .subsImm 31 3 8, .bcond 1 f5])
    (hf0 : cbField a tr = .ok f0) (hf1 : cbField (after a 1) tr = .ok f1)
    (hf3 : cbField (after a 3) tr = .ok f3) (hf5 : cbField (after a 5) tr = .ok f5)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io ∧
      t.pc = if s.x 0 = 0 ∧ s.x 1 = 0 ∧ s.x 2 = 1 ∧ s.x 3 = 8 then after a 6 else tr := by
  have c := fun k (hk : k < 6) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  have c23 : CodeAt code (after a 2) [.subsImm 31 2 1, .bcond 1 f3] := by
    simpa using CodeAt.drop_take code hcode 2 2 (by simp)
  have c45 : CodeAt code (after a 4) [.subsImm 31 3 8, .bcond 1 f5] := by
    simpa using CodeAt.drop_take code hcode 4 2 (by simp)
  have e1 : UInt64.ofNat (1 : Fin 4096).val = 1 := by decide
  have e8 : UInt64.ofNat (8 : Fin 4096).val = 8 := by decide
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbnz P code (s := s) (target := tr)
    (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hf0)
  by_cases h0 : s.x 0 = 0
  · rw [if_neg (by simpa using h0), hpc, ← after_one] at p1
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbnz P code (s := u1) (target := tr)
      (by rw [p1]; exact c1) (by rw [p1]; exact cbField_target hf1)
    by_cases h1 : s.x 1 = 0
    · rw [k1, if_neg (by simpa using h1), p1, ← after_succ] at p2
      obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_neImm P code (tB := tr) (by decide) c23
        (by rw [after_after]; exact cbField_target hf3) p2
      rw [e1, k2, k1] at p3
      by_cases h2 : s.x 2 = 1
      · rw [if_pos h2, after_after] at p3
        obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_neImm P code (tB := tr) (by decide) c45
          (by rw [after_after]; exact cbField_target hf5) p3
        rw [e8, k3, k2, k1, after_after] at p4
        refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), fun q => by rw [k4, k3, k2, k1],
          by rw [sp4, sp3, sp2, sp1], by rw [m4, m3, m2, m1], by rw [io4, io3, io2, io1], ?_⟩
        rw [p4]
        by_cases h3 : s.x 3 = 8
        · rw [if_pos h3, if_pos ⟨h0, h1, h2, h3⟩]
        · rw [if_neg h3, if_neg (fun h => h3 h.2.2.2)]
      · rw [if_neg h2] at p3
        exact ⟨u3, r1.trans (r2.trans r3), fun q => by rw [k3, k2, k1],
          by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1],
          by rw [p3, if_neg (fun h => h2 h.2.2.1)]⟩
    · rw [k1, if_pos h1] at p2
      exact ⟨u2, r1.trans r2, fun q => by rw [k2, k1], by rw [sp2, sp1], by rw [m2, m1],
        by rw [io2, io1], by rw [p2, if_neg (fun h => h1 h.2.1)]⟩
  · rw [if_pos h0] at p1
    exact ⟨u1, r1, k1, sp1, m1, io1, by rw [p1, if_neg (fun h => h0 h.1)]⟩

/-- The checks of an `fd_write` request, from `a`: descriptor 1 or 2, the iovec at 0, one iovec,
and the count at 8, or the trap stub.  X9 and the flags change. -/
theorem run_writeHead {a tr : UInt64} {f2 f3 f5 f7 : Fin 524288}
    (hcode : CodeAt code a [.subImm 9 0 1, .subsImm 31 9 1, .bcond 8 f2, .cbnz 1 f3,
      .subsImm 31 2 1, .bcond 1 f5, .subsImm 31 3 8, .bcond 1 f7])
    (hf2 : cbField (after a 2) tr = .ok f2) (hf3 : cbField (after a 3) tr = .ok f3)
    (hf5 : cbField (after a 5) tr = .ok f5) (hf7 : cbField (after a 7) tr = .ok f7)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (∀ q : Fin 32, q ≠ 9 → t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io ∧
      t.pc = if (s.x 0 = 1 ∨ s.x 0 = 2) ∧ s.x 1 = 0 ∧ s.x 2 = 1 ∧ s.x 3 = 8 then after a 8
        else tr := by
  have c := fun k (hk : k < 8) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c3 := c 3 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c3
  have c12 : CodeAt code (after a 1) [.subsImm 31 9 1, .bcond 8 f2] := by
    simpa using CodeAt.drop_take code hcode 1 2 (by simp)
  have c45 : CodeAt code (after a 4) [.subsImm 31 2 1, .bcond 1 f5] := by
    simpa using CodeAt.drop_take code hcode 4 2 (by simp)
  have c67 : CodeAt code (after a 6) [.subsImm 31 3 8, .bcond 1 f7] := by
    simpa using CodeAt.drop_take code hcode 6 2 (by simp)
  have e1 : UInt64.ofNat (1 : Fin 4096).val = 1 := by decide
  have e8 : UInt64.ofNat (8 : Fin 4096).val = 8 := by decide
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_setX P code (s := s) (i := .subImm 9 0 1)
    (d := 9) (v := s.x 0 - 1) (by decide) (by rw [hpc]; exact c0)
    (exec_subImm_x P (by decide) (by decide))
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_hiImm P code (tB := tr) (by decide) c12
    (by rw [after_after]; exact cbField_target hf2) q1
  rw [e1, x1] at p2
  have hfd : (1 < s.x 0 - 1) ↔ ¬ (s.x 0 = 1 ∨ s.x 0 = 2) := by
    constructor
    · intro h h'
      rcases h' with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
    · intro h
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.reduceToNat]
      have := (s.x 0).toNat_lt
      have h1 : (s.x 0).toNat ≠ 1 := fun e => h (.inl (UInt64.toNat_inj.mp e))
      have h2 : (s.x 0).toNat ≠ 2 := fun e => h (.inr (UInt64.toNat_inj.mp e))
      simp only [Nat.reducePow] at *
      omega
  have hk2 : ∀ q : Fin 32, q ≠ 9 → u2.x q = s.x q := fun q hq => by rw [k2, k1 q hq]
  by_cases hd : s.x 0 = 1 ∨ s.x 0 = 2
  · rw [if_neg (fun h => hfd.mp h hd), after_after] at p2
    obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_cbnz P code (s := u2) (target := tr)
      (by rw [p2]; exact c3) (by rw [p2]; exact cbField_target hf3)
    rw [hk2 1 (by decide)] at p3
    by_cases h1 : s.x 1 = 0
    · rw [if_neg (by simpa using h1), p2, ← after_succ] at p3
      obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_neImm P code (tB := tr) (by decide) c45
        (by rw [after_after]; exact cbField_target hf5) p3
      rw [e1, k3, hk2 2 (by decide)] at p4
      by_cases h2 : s.x 2 = 1
      · rw [if_pos h2, after_after] at p4
        obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_neImm P code (tB := tr) (by decide) c67
          (by rw [after_after]; exact cbField_target hf7) p4
        rw [e8, k4, k3, hk2 3 (by decide), after_after] at p5
        refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))),
          fun q hq => by rw [k5, k4, k3, hk2 q hq], by rw [sp5, sp4, sp3, sp2, sp1],
          by rw [m5, m4, m3, m2, m1], by rw [io5, io4, io3, io2, io1], ?_⟩
        rw [p5]
        by_cases h3 : s.x 3 = 8
        · rw [if_pos h3, if_pos ⟨hd, h1, h2, h3⟩]
        · rw [if_neg h3, if_neg (fun h => h3 h.2.2.2)]
      · rw [if_neg h2] at p4
        exact ⟨u4, r1.trans (r2.trans (r3.trans r4)), fun q hq => by rw [k4, k3, hk2 q hq],
          by rw [sp4, sp3, sp2, sp1], by rw [m4, m3, m2, m1], by rw [io4, io3, io2, io1],
          by rw [p4, if_neg (fun h => h2 h.2.2.1)]⟩
    · rw [if_pos h1] at p3
      exact ⟨u3, r1.trans (r2.trans r3), fun q hq => by rw [k3, hk2 q hq],
        by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1],
        by rw [p3, if_neg (fun h => h1 h.2.1)]⟩
  · rw [if_pos (hfd.mpr hd)] at p2
    exact ⟨u2, r1.trans r2, hk2, by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1],
      by rw [p2, if_neg (fun h => hd h.1)]⟩

/-- The check of a read's buffer above the guest's first 16 bytes, from `a`: a buffer of no byte
or a pointer of at least 16 reaches `after a 4` with X0 at 0, and any other the trap stub. -/
theorem run_readLow {a tr : UInt64} {f0 f2 : Fin 524288}
    (hcode : CodeAt code a [.cbz 11 f0, .subsImm 31 10 16, .bcond 3 f2, .movz 0 0 0])
    (hf0 : cbField a (after a 3) = .ok f0) (hf2 : cbField (after a 2) tr = .ok f2)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (∀ q : Fin 32, q ≠ 0 → t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io ∧
      if s.x 11 = 0 ∨ 16 ≤ s.x 10 then t.pc = after a 4 ∧ t.x 0 = 0 else t.pc = tr := by
  have c := fun k (hk : k < 4) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c3 := c 3 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c3
  have c12 : CodeAt code (after a 1) [.subsImm 31 10 16, .bcond 3 f2] := by
    simpa using CodeAt.drop_take code hcode 1 2 (by simp)
  have e16 : UInt64.ofNat (16 : Fin 4096).val = 16 := by decide
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbz P code (s := s) (target := after a 3)
    (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hf0)
  have hz : ∀ u : State, Reach P code s u → (∀ q : Fin 32, u.x q = s.x q) → u.sp = s.sp →
      u.mem = s.mem → u.io = s.io → u.pc = after a 3 →
      ∃ t, Reach P code s t ∧ (∀ q : Fin 32, q ≠ 0 → t.x q = s.x q) ∧ t.sp = s.sp ∧
        t.mem = s.mem ∧ t.io = s.io ∧ t.pc = after a 4 ∧ t.x 0 = 0 := by
    intro u ru ku spu mu iou pu
    obtain ⟨t, rt, pt, xt, kt, spt, mt, iot⟩ := step_movz P code (s := u) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [pu]; exact c3)
    exact ⟨t, ru.trans rt, fun q hq => by rw [kt q hq, ku], by rw [spt, spu],
      by rw [mt, mu], by rw [iot, iou], by rw [pt, pu, ← after_succ],
      by rw [xt, movz0_val]; decide⟩
  by_cases h0 : s.x 11 = 0
  · rw [if_pos h0] at p1
    obtain ⟨t, rt, kt, spt, mt, iot, pt, xt⟩ := hz u1 r1 k1 sp1 m1 io1 p1
    exact ⟨t, rt, kt, spt, mt, iot, by rw [if_pos (.inl h0)]; exact ⟨pt, xt⟩⟩
  · rw [if_neg h0, hpc, ← after_one] at p1
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_loImm P code (tB := tr) (by decide) c12
      (by rw [after_after]; exact cbField_target hf2) p1
    rw [e16, k1] at p2
    by_cases h16 : s.x 10 < 16
    · rw [if_pos h16] at p2
      exact ⟨u2, r1.trans r2, fun q _ => by rw [k2, k1], by rw [sp2, sp1], by rw [m2, m1],
        by rw [io2, io1], by
          rw [if_neg (fun h => h.elim h0 (fun h' => absurd h16 (UInt64.not_lt.mpr h')))]
          exact p2⟩
    · rw [if_neg h16, after_after] at p2
      obtain ⟨t, rt, kt, spt, mt, iot, pt, xt⟩ := hz u2 (r1.trans r2)
        (fun q => by rw [k2, k1]) (by rw [sp2, sp1]) (by rw [m2, m1]) (by rw [io2, io1]) p2
      exact ⟨t, rt, kt, spt, mt, iot, by
        rw [if_pos (.inr (UInt64.not_lt.mp h16))]
        exact ⟨pt, xt⟩⟩

/-- `readStub` unpacked. -/
theorem readStub_ok {a svc tr en : UInt64} {is : List Instr} (hg : readStub a svc tr en = .ok is) :
    ∃ f0 f1 f3 f5 f17 f19 checks call tail,
      cbField a tr = .ok f0 ∧ cbField (after a 1) tr = .ok f1 ∧
      cbField (after a 3) tr = .ok f3 ∧ cbField (after a 5) tr = .ok f5 ∧
      bufferChecks (after a 6) tr = .ok checks ∧ cbField (after a 17) (after a 20) = .ok f17 ∧
      cbField (after a 19) tr = .ok f19 ∧ bufferCall (after a 21) svc 63 = .ok call ∧
      resultTail (after a 28) tr en = .ok tail ∧
      is = [.cbnz 0 f0, .cbnz 1 f1, .subsImm 31 2 1, .bcond 1 f3, .subsImm 31 3 8, .bcond 1 f5] ++
        checks ++ [.cbz 11 f17, .subsImm 31 10 16, .bcond 3 f19, .movz 0 0 0] ++ call ++ tail := by
  unfold readStub at hg
  cases h0 : cbField a tr with
  | error err => simp [h0, bind, Except.bind] at hg
  | ok f0 =>
  cases h1 : cbField (after a 1) tr with
  | error err => simp [h0, h1, bind, Except.bind] at hg
  | ok f1 =>
  cases h3 : cbField (after a 3) tr with
  | error err => simp [h0, h1, h3, bind, Except.bind] at hg
  | ok f3 =>
  cases h5 : cbField (after a 5) tr with
  | error err => simp [h0, h1, h3, h5, bind, Except.bind] at hg
  | ok f5 =>
  cases hc : bufferChecks (after a 6) tr with
  | error err => simp [h0, h1, h3, h5, hc, bind, Except.bind] at hg
  | ok checks =>
  cases h17 : cbField (after a 17) (after a 20) with
  | error err => simp [h0, h1, h3, h5, hc, h17, bind, Except.bind] at hg
  | ok f17 =>
  cases h19 : cbField (after a 19) tr with
  | error err => simp [h0, h1, h3, h5, hc, h17, h19, bind, Except.bind] at hg
  | ok f19 =>
  cases hcall : bufferCall (after a 21) svc 63 with
  | error err => simp [h0, h1, h3, h5, hc, h17, h19, hcall, bind, Except.bind] at hg
  | ok call =>
  cases ht : resultTail (after a 28) tr en with
  | error err => simp [h0, h1, h3, h5, hc, h17, h19, hcall, ht, bind, Except.bind] at hg
  | ok tail =>
  simp only [h0, h1, h3, h5, hc, h17, h19, hcall, ht, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  exact ⟨f0, f1, f3, f5, f17, f19, checks, call, tail, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, hg.symm⟩

/-- `writeStub` unpacked. -/
theorem writeStub_ok {a svc tr en : UInt64} {is : List Instr}
    (hg : writeStub a svc tr en = .ok is) :
    ∃ f2 f3 f5 f7 checks call tail,
      cbField (after a 2) tr = .ok f2 ∧ cbField (after a 3) tr = .ok f3 ∧
      cbField (after a 5) tr = .ok f5 ∧ cbField (after a 7) tr = .ok f7 ∧
      bufferChecks (after a 8) tr = .ok checks ∧ bufferCall (after a 19) svc 64 = .ok call ∧
      resultTail (after a 26) tr en = .ok tail ∧
      is = [.subImm 9 0 1, .subsImm 31 9 1, .bcond 8 f2, .cbnz 1 f3, .subsImm 31 2 1, .bcond 1 f5,
        .subsImm 31 3 8, .bcond 1 f7] ++ checks ++ call ++ tail := by
  unfold writeStub at hg
  cases h2 : cbField (after a 2) tr with
  | error err => simp [h2, bind, Except.bind] at hg
  | ok f2 =>
  cases h3 : cbField (after a 3) tr with
  | error err => simp [h2, h3, bind, Except.bind] at hg
  | ok f3 =>
  cases h5 : cbField (after a 5) tr with
  | error err => simp [h2, h3, h5, bind, Except.bind] at hg
  | ok f5 =>
  cases h7 : cbField (after a 7) tr with
  | error err => simp [h2, h3, h5, h7, bind, Except.bind] at hg
  | ok f7 =>
  cases hc : bufferChecks (after a 8) tr with
  | error err => simp [h2, h3, h5, h7, hc, bind, Except.bind] at hg
  | ok checks =>
  cases hcall : bufferCall (after a 19) svc 64 with
  | error err => simp [h2, h3, h5, h7, hc, hcall, bind, Except.bind] at hg
  | ok call =>
  cases ht : resultTail (after a 26) tr en with
  | error err => simp [h2, h3, h5, h7, hc, hcall, ht, bind, Except.bind] at hg
  | ok tail =>
  simp only [h2, h3, h5, h7, hc, hcall, ht, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  exact ⟨f2, f3, f5, f7, checks, call, tail, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg.symm⟩

end LeanExe.A64
