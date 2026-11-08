import LeanExe.M7.Init
import LeanExe.M7.Proof.Boot

/-!
The run of a board's initialization of `LeanExe/M7/Init.lean`.  `run_op` runs the code of one
access whose address is a device register: a read appends the read of the register with the next
value of `σ`, and a write appends the write of the value that `opTrace` names, for a
read-modify-write the value read with the masks applied.  `init_runs` composes the accesses by
induction on the list, which gives `InitRuns` with the trace `initTrace ops` and `initReads ops`
reads.
-/

namespace LeanExe.M7

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-- A word access at `a` is an access to a device register. -/
def DevReg (P : Platform) (a : UInt32) : Prop := a % 4 = 0 ∧ P.device a = true

/-- The address of the access `op` is a device register. -/
def OpOk (P : Platform) : InitOp → Prop
  | .rmw a _ _ => DevReg P a
  | .read a => DevReg P a
  | .write a _ => DevReg P a
  | .dsb => True

theorem opCode_wide (op : InitOp) : (opCode op).all Instr.wide = true := by
  cases op <;> rfl

theorem initCode_cons (op : InitOp) (ops : List InitOp) :
    initCode (op :: ops) = opCode op ++ initCode ops := by
  simp only [initCode, List.flatMap_cons]

theorem initCode_wide : ∀ ops : List InitOp, (initCode ops).all Instr.wide = true
  | [] => rfl
  | op :: ops => by
      rw [initCode_cons, List.all_append, opCode_wide, initCode_wide ops]
      rfl

/-- `MOVW` and `MOVT` set register `d` to `w` and keep the other registers, SP, the trace, and
the read count. -/
theorem run_movWord {s : State} {d : Fin 8} {w : UInt32} {rest : List Instr}
    (hc : CodeAt code s.pc (movWord d w ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + 8 ∧ t.sp = s.sp ∧
      t.trace = s.trace ∧ t.reads = s.reads ∧ t.r d = w ∧ (∀ e, e ≠ d → t.r e = s.r e) ∧
      t.mem = s.mem := by
  have hw := toNat_lt32 w
  obtain ⟨c1, c2⟩ := CodeAt.append.mp hc
  obtain ⟨r, p, sp, -, tr, rd, -⟩ :=
    run_slots (P := P) (σ := σ) (slotsOk_reg (movWord_regForm d w) s.sp) c1
  have hp : (slotRun P σ (movWord d w) s).pc = s.pc + 8 := by rw [p]; rfl
  refine ⟨_, r, ?_, hp, sp, tr, rd, ?_, fun e he => ?_, rfl⟩
  · rw [hp]
    exact c2
  · simp only [movWord, Instr.movwOf, Instr.movtOf, slotRun_cons, slotRun_nil, slotStep, exec,
      Option.getD_some]
    rw [State.r_withPc, State.r_setR_same, State.r_withPc, State.r_setR_same,
      imm16_field (by omega), imm16_field (by omega), dev_word]
  · simp only [movWord, Instr.movwOf, Instr.movtOf, slotRun_cons, slotRun_nil, slotStep, exec,
      Option.getD_some]
    rw [State.r_withPc, State.r_setR_ne _ _ he, State.r_withPc, State.r_setR_ne _ _ he]

/-- A word load of the device register at `a`, the address in register `n`. -/
theorem exec_ldrDev {s : State} {t n : Fin 8} {a : UInt32} (ha : s.r n = a) (hd : DevReg P a) :
    exec P σ (.ldr t n 0) s =
      some { ({ s with trace := s.trace ++ [Access.read a (σ s.reads)], reads := s.reads + 1 } :
        State).setR t (σ s.reads) with pc := s.pc + 4 } := by
  simp only [exec, loadWord, ha, show UInt32.ofNat (0 : Fin 4096).val = 0 from rfl,
    UInt32.add_zero, hd.1, hd.2, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_some]

/-- A word store of register `t` to the device register at `a`, the address in register `n`. -/
theorem exec_strDev {s : State} {t n : Fin 8} {a : UInt32} (ha : s.r n = a) (hd : DevReg P a) :
    exec P σ (.str t n 0) s =
      some { ({ s with trace := s.trace ++ [Access.write a (s.r t)] } : State) with
        pc := s.pc + 4 } := by
  simp only [exec, storeWord, ha, show UInt32.ofNat (0 : Fin 4096).val = 0 from rfl,
    UInt32.add_zero, hd.1, hd.2, ne_eq, not_true_eq_false, ↓reduceIte, Option.map_some]

/-- The read of the device register at `a`, whose address `r0` holds, into r1. -/
theorem run_ldrDev {s : State} {a : UInt32} {rest : List Instr} (hd : DevReg P a)
    (ha : s.r 0 = a) (hc : CodeAt code s.pc (.ldr 1 0 0 :: rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + 4 ∧ t.sp = s.sp ∧
      t.trace = s.trace ++ [Access.read a (σ s.reads)] ∧ t.reads = s.reads + 1 ∧
      t.r 1 = σ s.reads ∧ t.r 0 = a ∧ t.mem = s.mem := by
  obtain ⟨u, hu⟩ : ∃ u : State, u =
      { ({ s with trace := s.trace ++ [Access.read a (σ s.reads)], reads := s.reads + 1 } :
        State).setR 1 (σ s.reads) with pc := s.pc + 4 } := ⟨_, rfl⟩
  have e : exec P σ (.ldr 1 0 0) s = some u := by rw [hu]; exact exec_ldrDev ha hd
  obtain ⟨r, c, p⟩ := reach_falls hc rfl e
  refine ⟨u, r, c, p, by subst hu; rfl, by subst hu; rfl, by subst hu; rfl, ?_, ?_,
    by subst hu; rfl⟩
  · rw [hu, State.r_withPc, State.r_setR_same]
  · rw [hu, State.r_withPc, State.r_setR_ne _ _ (by decide)]
    exact ha

/-- The write of r1 to the device register at `a`, whose address `r0` holds. -/
theorem run_strDev {s : State} {a : UInt32} {rest : List Instr} (hd : DevReg P a)
    (ha : s.r 0 = a) (hc : CodeAt code s.pc (.str 1 0 0 :: rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + 4 ∧ t.sp = s.sp ∧
      t.trace = s.trace ++ [Access.write a (s.r 1)] ∧ t.reads = s.reads ∧ t.mem = s.mem := by
  obtain ⟨u, hu⟩ : ∃ u : State, u = { ({ s with trace := s.trace ++ [Access.write a (s.r 1)] } :
      State) with pc := s.pc + 4 } := ⟨_, rfl⟩
  have e : exec P σ (.str 1 0 0) s = some u := by rw [hu]; exact exec_strDev ha hd
  obtain ⟨r, c, p⟩ := reach_falls hc rfl e
  exact ⟨u, r, c, p, by subst hu; rfl, by subst hu; rfl, by subst hu; rfl, by subst hu; rfl⟩

/-- A register form that does not branch, followed by more code: a step reaches the code after it
and keeps SP, the trace, and the read count. -/
theorem run_reg {s u : State} {i : Instr} {rest : List Instr} (hc : CodeAt code s.pc (i :: rest))
    (hr : i.regOnly = true) (hf : i.falls = true) (he : exec P σ i s = some u) :
    Reach P σ code s u ∧ CodeAt code u.pc rest ∧ u.pc = s.pc + 4 ∧ Keeps s u :=
  let ⟨r, c, p⟩ := reach_falls hc hf he
  ⟨r, c, p, exec_keeps hr he⟩

theorem run_rmw {s : State} {a c v : UInt32} {rest : List Instr} (hd : DevReg P a)
    (hc : CodeAt code s.pc (opCode (.rmw a c v) ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + UInt32.ofNat 40 ∧
      t.sp = s.sp ∧ t.trace = s.trace ++ opTrace (.rmw a c v) (σ s.reads) ∧
      t.reads = s.reads + 1 ∧ t.mem = s.mem := by
  simp only [opCode, List.append_assoc, List.cons_append, List.nil_append] at hc
  obtain ⟨t1, r1, c1, p1, sp1, tr1, rd1, a1, -, mm1⟩ := run_movWord (P := P) (σ := σ) hc
  obtain ⟨t2, r2, c2, p2, sp2, tr2, rd2, v2, a2, mm2⟩ := run_ldrDev (P := P) (σ := σ) hd a1 c1
  obtain ⟨t3, r3, c3, p3, sp3, tr3, rd3, m3, k3, mm3⟩ := run_movWord (P := P) (σ := σ) c2
  obtain ⟨u4, hu4⟩ : ∃ u4 : State, u4 = { t3.setR 1 (t3.r 1 &&& t3.r 2) with pc := t3.pc + 4 } :=
    ⟨_, rfl⟩
  obtain ⟨r4, c4, p4, k4⟩ := run_reg (P := P) (σ := σ) c3 rfl rfl
    (show exec P σ (.andReg 1 1 2) t3 = some u4 by rw [hu4]; rfl)
  have v4 : u4.r 1 = σ s.reads &&& ~~~c := by
    rw [hu4, State.r_withPc, State.r_setR_same, k3 1 (by decide), v2, m3, rd1]
  have a4 : u4.r 0 = a := by
    rw [hu4, State.r_withPc, State.r_setR_ne _ _ (by decide), k3 0 (by decide), a2]
  obtain ⟨t5, r5, c5, p5, sp5, tr5, rd5, m5, k5, mm5⟩ := run_movWord (P := P) (σ := σ) c4
  obtain ⟨u6, hu6⟩ : ∃ u6 : State,
      u6 = { t5.result 0 1 (t5.r 1 ||| t5.r 2, t5.cFlag, t5.vFlag) with pc := t5.pc + 4 } :=
    ⟨_, rfl⟩
  obtain ⟨r6, c6, p6, k6⟩ := run_reg (P := P) (σ := σ) c5 rfl rfl
    (show exec P σ (.orrReg 0 1 1 2) t5 = some u6 by rw [hu6]; rfl)
  have v6 : u6.r 1 = σ s.reads &&& ~~~c ||| v := by
    rw [hu6, State.r_withPc, State.r_result_zero, State.r_setR_same, k5 1 (by decide), v4, m5]
  have a6 : u6.r 0 = a := by
    rw [hu6, State.r_withPc, State.r_result_zero, State.r_setR_ne _ _ (by decide),
      k5 0 (by decide), a4]
  obtain ⟨t7, r7, c7, p7, sp7, tr7, rd7, mm7⟩ := run_strDev (P := P) (σ := σ) hd a6 c6
  refine ⟨t7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))), c7, ?_, ?_, ?_,
    ?_, by rw [mm7, k6.mem, mm5, k4.mem, mm3, mm2, mm1]⟩
  · rw [p7, p6, p5, p4, p3, p2, p1]
    addr_eq
  · rw [sp7, k6.sp, sp5, k4.sp, sp3, sp2, sp1]
  · rw [tr7, k6.trace, tr5, k4.trace, tr3, tr2, tr1, rd1, v6, List.append_assoc]
    rfl
  · rw [rd7, k6.reads, rd5, k4.reads, rd3, rd2, rd1]

theorem run_readOp {s : State} {a : UInt32} {rest : List Instr} (hd : DevReg P a)
    (hc : CodeAt code s.pc (opCode (.read a) ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + UInt32.ofNat 12 ∧
      t.sp = s.sp ∧ t.trace = s.trace ++ opTrace (.read a) (σ s.reads) ∧
      t.reads = s.reads + 1 ∧ t.mem = s.mem := by
  simp only [opCode, List.append_assoc, List.cons_append, List.nil_append] at hc
  obtain ⟨t1, r1, c1, p1, sp1, tr1, rd1, a1, -, mm1⟩ := run_movWord (P := P) (σ := σ) hc
  obtain ⟨t2, r2, c2, p2, sp2, tr2, rd2, -, -, mm2⟩ := run_ldrDev (P := P) (σ := σ) hd a1 c1
  refine ⟨t2, r1.trans r2, c2, ?_, by rw [sp2, sp1], ?_, by rw [rd2, rd1], by rw [mm2, mm1]⟩
  · rw [p2, p1]
    addr_eq
  · rw [tr2, tr1, rd1]
    rfl

theorem run_writeOp {s : State} {a v : UInt32} {rest : List Instr} (hd : DevReg P a)
    (hc : CodeAt code s.pc (opCode (.write a v) ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + UInt32.ofNat 20 ∧
      t.sp = s.sp ∧ t.trace = s.trace ++ opTrace (.write a v) (σ s.reads) ∧
      t.reads = s.reads ∧ t.mem = s.mem := by
  simp only [opCode, List.append_assoc, List.cons_append, List.nil_append] at hc
  obtain ⟨t1, r1, c1, p1, sp1, tr1, rd1, a1, -, mm1⟩ := run_movWord (P := P) (σ := σ) hc
  obtain ⟨t2, r2, c2, p2, sp2, tr2, rd2, v2, k2, mm2⟩ := run_movWord (P := P) (σ := σ) c1
  obtain ⟨t3, r3, c3, p3, sp3, tr3, rd3, mm3⟩ := run_strDev (P := P) (σ := σ) hd
    (by rw [k2 0 (by decide), a1]) c2
  refine ⟨t3, r1.trans (r2.trans r3), c3, ?_, by rw [sp3, sp2, sp1], ?_, by rw [rd3, rd2, rd1],
    by rw [mm3, mm2, mm1]⟩
  · rw [p3, p2, p1]
    addr_eq
  · rw [tr3, tr2, tr1, v2]
    rfl

theorem run_dsbOp {s : State} {rest : List Instr}
    (hc : CodeAt code s.pc (opCode .dsb ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧ t.pc = s.pc + UInt32.ofNat 4 ∧
      t.sp = s.sp ∧ t.trace = s.trace ++ opTrace .dsb (σ s.reads) ∧ t.reads = s.reads ∧
      t.mem = s.mem := by
  simp only [opCode, List.cons_append, List.nil_append] at hc
  obtain ⟨r, c, p⟩ := reach_falls (P := P) (σ := σ) (u := { s with pc := s.pc + 4 }) hc rfl rfl
  exact ⟨_, r, c, p, rfl, (List.append_nil _).symm, rfl, rfl⟩

/-- The code of an access whose address is a device register, followed by more code. -/
theorem run_op {s : State} {op : InitOp} {rest : List Instr} (hd : OpOk P op)
    (hc : CodeAt code s.pc (opCode op ++ rest)) :
    ∃ t, Reach P σ code s t ∧ CodeAt code t.pc rest ∧
      t.pc = s.pc + UInt32.ofNat (4 * (opCode op).length) ∧ t.sp = s.sp ∧
      t.trace = s.trace ++ opTrace op (σ s.reads) ∧ t.reads = s.reads + opReads op ∧
      t.mem = s.mem := by
  cases op with
  | rmw a c v => exact run_rmw (a := a) (c := c) (v := v) hd hc
  | read a => exact run_readOp (a := a) hd hc
  | write a v => exact run_writeOp (a := a) (v := v) hd hc
  | dsb => exact run_dsbOp hc

/-- An initialization whose addresses are device registers runs with the trace `initTrace ops`
of the values that its reads return and `initReads ops` reads, and it keeps memory, since a
device access changes no byte of it. -/
theorem init_runs : ∀ ops : List InitOp, (∀ op ∈ ops, OpOk P op) →
    InitRuns P σ code (initCode ops) (initTrace ops) (initReads ops)
  | [], _ => fun s _ =>
      ⟨s, .refl _, by
        show s.pc = s.pc + UInt32.ofNat 0
        rw [show UInt32.ofNat 0 = 0 from rfl, UInt32.add_zero], rfl, (List.append_nil _).symm,
        rfl, rfl⟩
  | op :: ops, h => fun s hc => by
      rw [initCode_cons] at hc
      obtain ⟨t1, r1, c1, p1, sp1, tr1, rd1, mm1⟩ := run_op (h op List.mem_cons_self) hc
      obtain ⟨t2, r2, p2, sp2, tr2, rd2, mm2⟩ :=
        init_runs ops (fun o ho => h o (List.mem_cons_of_mem _ ho)) t1 c1
      have hf : (fun j => σ (j + (s.reads + opReads op))) =
          fun j => σ (j + opReads op + s.reads) := by
        funext j
        congr 1
        omega
      refine ⟨t2, r1.trans r2, ?_, sp2.trans sp1, ?_, ?_, mm2.trans mm1⟩
      · rw [p2, p1, add_ofNat_add, initCode_cons, List.length_append, Nat.mul_add]
      · rw [tr2, tr1, rd1, hf, List.append_assoc]
        simp only [initTrace, Nat.zero_add]
      · rw [rd2, rd1]
        simp only [initReads, List.map_cons, List.sum_cons]
        omega

end LeanExe.M7
