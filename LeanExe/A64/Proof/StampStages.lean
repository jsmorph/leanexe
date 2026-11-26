module

public import LeanExe.A64.Proof.StampLoops

@[expose] public section

/-!
The stages of the stamp program's routine after the allocation, with the block's address in
X19.  `stamp_open` follows `clock_gettime` into the block's first 16 bytes, `getrandom` into the
next 16, the stores of the input path's words into the frame, and the `openat` of the input, to
the head of the read loop with the descriptor in the frame's slot 2, or to the stub of status 72,
73, or 67.  `stamp_read` follows the read loop, the store of the count, the input's `close`, and
the call of the function, and `stamp_output` the stores of the output path's words, the output's
`openat`, the write loop, the output's `close`, and the return.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies readCall writeCall readData writeData)

variable {T : List Call} {R : Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-- `SUBS XZR, X0, #16` and `B.NE` at `a`: the run reaches `tB` when X0 is not 16 and the next
instruction otherwise, changing the flags alone. -/
theorem run_ne16 {a tB : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.subsImm 31 0 16, .bcond 1 g]) (hg : cbField (after a 1) tB = .ok g)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x 0 = 16 then after a 2 else tB) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x 0) (UInt64.ofNat 16) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsImm 31 0 16) s = some s1 := rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 1 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 1 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_one]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x 0 - UInt64.ofNat 16)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 1 = !decide (s.x 0 = 16) := by
    show (!(s.subs 31 (s.x 0) (UInt64.ofNat 16)).zFlag) = _
    rw [subs_z]
    rfl
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 1 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : s.x 0 = 16
    · rw [ite_eq_right (by simp [h]), ite_eq_left h, ← after_succ]
    · rw [ite_eq_left (by simpa using h), ite_eq_right h]
      exact cbField_target hg
  · show (s.setX 31 (s.x 0 - UInt64.ofNat 16)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x 0 - UInt64.ofNat 16)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x 0 - UInt64.ofNat 16)).io = _
    exact State.setX_io

theorem pathOk_facts {path : List UInt8} (h : pathOk path = true) :
    0 < path.length ∧ path.length < 64 ∧ ∀ i < path.length, path.getD i 0 ≠ 0 := by
  unfold pathOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun i hi he => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at he
  have hm : (0 : UInt8) ∈ path := he ▸ List.getElem_mem hi
  have : path.contains 0 = true := List.elem_iff.mpr hm
  rw [h3] at this
  cases this

/-- A byte of the frame at `sp` below slot `j` lies outside the slots from `j` on. -/
theorem below_slots {sp : UInt64} {i j n : Nat} (hi : i < j)
    (hn : j + n < 512) (k : Nat) (hk : k < 8) :
    ¬ (slotAddr sp i + UInt64.ofNat k - slotAddr sp j).toNat < 8 * n := by
  rw [UInt64.toNat_sub, UInt64.toNat_add, toNat_slot, toNat_slot, UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

/-- The bytes of slot `i` of the frame at `sp` lie at or above `sp`. -/
theorem slot_le {sp : UInt64} {i k : Nat} (hsp : sp.toNat < 2 ^ 63) (hi : i < 512) (hk : k < 8) :
    sp.toNat ≤ (slotAddr sp i + UInt64.ofNat k).toNat := by
  have := le_slot (sp := sp) (i := i) (m := 0) (k := k) hk hsp (by omega) (Nat.zero_le _)
  omega

/-! ## The calls before the read loop -/

theorem table_clock : LeanExe.Linux.table.find? (fun c => c.arm64 == 113) =
    some LeanExe.Linux.clockGettimeCall := rfl
theorem table_random : LeanExe.Linux.table.find? (fun c => c.arm64 == 278) =
    some LeanExe.Linux.getrandomCall := rfl
theorem table_openat : LeanExe.Linux.table.find? (fun c => c.arm64 == 56) =
    some LeanExe.Linux.openatCall := rfl
theorem table_close : LeanExe.Linux.table.find? (fun c => c.arm64 == 57) =
    some LeanExe.Linux.closeCall := rfl
theorem table_read : LeanExe.Linux.table.find? (fun c => c.arm64 == 63) =
    some LeanExe.Linux.readCall := rfl
theorem table_write : LeanExe.Linux.table.find? (fun c => c.arm64 == 64) =
    some LeanExe.Linux.writeCall := rfl

/-- The address of byte `4096 + root + j` of the area at `area`, as `ReadStore` names it. -/
theorem block_addr (area : UInt64) (root j : Nat) :
    area + UInt64.ofNat (4096 + root) + UInt64.ofNat j = area + UInt64.ofNat (4096 + (root + j)) := by
  rw [add_ofNat_add, Nat.add_assoc]

/-- From the state after the allocation of the block at `B` in the area, held in X19: the call of
`clock_gettime` into the block's first 16 bytes and of `getrandom` into the next 16, the stores of
the input path's words into the frame's slots from 4, and the `openat` of the input path.  The run
reaches the exit word with status 72, 73, or 67, with the events of `StampEvents`; or it reaches
the head of the read loop with the descriptor in the frame's slot 2, X1 at the block's byte 32,
X2 at `inMax + 1`, and the block holding the clock's and the random bytes. -/
theorem stamp_open {a svc e72 e73 e67 base : UInt64} {c20 c26 cI x72 x73 x67 : Fin 67108864}
    {f72 f73 f67 : Fin 524288} {inMax area sp0 : UInt64} {cap : Nat} {gts : List ValueType}
    {st1 : Store Unit} {root : Nat} {pin pout : List UInt8} {sIn : List Instr}
    {Out : List UInt8 → List UInt8} {Tr : List UInt8 → UInt64 → Prop}
    (hc : CodeAt code a [.movz 0 0 0, .addImm 1 19 0, .movz 8 113 0, .bl c20, .cbnz 0 f72,
      .addImm 0 19 16, .movz 1 16 0, .movz 2 0 0, .movz 8 278 0, .bl c26, .subsImm 31 0 16,
      .bcond 1 f73])
    (hc20 : bField (after a 3) svc = .ok c20) (hf72 : cbField (after a 4) e72 = .ok f72)
    (hc26 : bField (after a 9) svc = .ok c26) (hf73 : cbField (after a 11) e73 = .ok f73)
    (hsIn : storeWords (pathWords pin) 4 = .ok sIn) (hcIn : CodeAt code (after a 12) sIn)
    (hco : CodeAt code (after a (12 + 5 * (pathWords pin).length))
      (movImm 0 atFdcwd ++ [.addImm 1 31 32] ++ movImm 2 stampInFlags ++
        [.movz 3 0 0, .movz 8 56 0, .bl cI, .lsrImm 16 0 31, .cbnz 16 f67, .str 0 31 2]))
    (hco2 : CodeAt code (after a (27 + 5 * (pathWords pin).length))
      ([.addImm 1 19 32] ++ movImm 2 (inMax + 1)))
    (hcI : bField (after (after a (12 + 5 * (pathWords pin).length)) 11) svc = .ok cI)
    (hf67 : cbField (after (after a (12 + 5 * (pathWords pin).length)) 13) e67 = .ok f67)
    (hs72 : CodeAt code e72 (movImm 0 (UInt64.ofNat 72) ++ [.b x72]))
    (hx72 : bField (after e72 4) base = .ok x72)
    (hs73 : CodeAt code e73 (movImm 0 (UInt64.ofNat 73) ++ [.b x73]))
    (hx73 : bField (after e73 4) base = .ok x73)
    (hs67 : CodeAt code e67 (movImm 0 (UInt64.ofNat 67) ++ [.b x67]))
    (hx67 : bField (after e67 4) base = .ok x67)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (hbase : base.toNat < 2 ^ 55)
    (hend : (after a (32 + 5 * (pathWords pin).length)).toNat < 2 ^ 55)
    (hpin : pathOk pin = true)
    (hF : 32 + 8 * (pathWords pin).length ≤ stampFrame pin pout)
    (hin : inMax.toNat < 2 ^ 32)
    {q : Proc} (hpc : q.core.pc = a) (hf : q.fpcr = fpcrValue) (htr : q.trace = [])
    (hsp : q.core.sp = sp0 - UInt64.ofNat (stampFrame pin pout))
    (hal : (sp0 - UInt64.ofNat (stampFrame pin pout)) % 16 = 0)
    (htop : (sp0 - UInt64.ofNat (stampFrame pin pout)).toNat < 2 ^ 63)
    (hframe : ∀ j < stampFrame pin pout,
      P.normal (sp0 - UInt64.ofNat (stampFrame pin pout) + UInt64.ofNat j) = true)
    (h17 : q.core.x 17 = area)
    (h18 : (q.core.x 18).toNat ≤ (sp0 - UInt64.ofNat (stampFrame pin pout)).toNat)
    (h19 : q.core.x 19 = area + UInt64.ofNat (4096 + root))
    (hst : ReadStore P cap gts st1 root (inMax.toNat + 33) [] q.core)
    (hN : root + (inMax.toNat + 33) ≤ st1.mem.pages * 65536)
    (hB : area.toNat + 4096 + root + inMax.toNat + 33 ≤
      sp0.toNat - stampFrame pin pout) :
    (∃ q', ProcReachWith LeanExe.Linux.table R P code q q' ∧ q'.core.io = q.core.io ∧
      q'.core.pc = base ∧
      StampEvents sp0 inMax pin pout Out Tr (some (q'.core.x 0)) (sysEvents q'.trace)) ∨
    (∃ q' ec er eo, ProcReachWith LeanExe.Linux.table R P code q q' ∧
      q'.fpcr = fpcrValue ∧ q'.core.io = q.core.io ∧
      StampOpened sp0 inMax pin pout (area + UInt64.ofNat (4096 + root)) ec er eo ∧
      ec.output.length = 16 ∧ er.output.length = 16 ∧
      sysEvents q'.trace = [ec, er, eo] ∧
      q'.core.pc = after a (32 + 5 * (pathWords pin).length) ∧
      q'.core.sp = q.core.sp ∧ q'.core.x 17 = area ∧ q'.core.x 18 = q.core.x 18 ∧
      q'.core.x 1 = area + UInt64.ofNat (4096 + (root + 32)) ∧
      q'.core.x 2 = UInt64.ofNat (inMax.toNat + 1) ∧
      load64 q'.core.mem (slotAddr (sp0 - UInt64.ofNat (stampFrame pin pout)) 2) = eo.ret ∧
      (∀ i < 2, load64 q'.core.mem (slotAddr (sp0 - UInt64.ofNat (stampFrame pin pout)) i) =
        load64 q.core.mem (slotAddr (sp0 - UInt64.ofNat (stampFrame pin pout)) i)) ∧
      ReadStore P cap gts st1 root (inMax.toNat + 33) (ec.output ++ er.output) q'.core) := by
  generalize hSPf : sp0 - UInt64.ofNat (stampFrame pin pout) = SPf at *
  generalize hBdef : area + UInt64.ofNat (4096 + root) = B at h19
  obtain ⟨hpl0, hpl64, hnz⟩ := pathOk_facts hpin
  have hwl : (pathWords pin).length = pin.length / 8 + 1 := pathWords_length pin
  have hsp0n := sp0.toNat_lt
  have hBn : B.toNat = area.toNat + 4096 + root := by
    rw [← hBdef, UInt64.toNat_add, UInt64.toNat_ofNat']
    simp only [Nat.reducePow] at *
    omega
  have hB' : B.toNat + inMax.toNat + 33 ≤ sp0.toNat - stampFrame pin pout := by omega
  have hBj : ∀ j : Nat, B + UInt64.ofNat j = q.core.x 17 + UInt64.ofNat (4096 + (root + j)) :=
    fun j => by rw [h17, ← hBdef, block_addr]
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  have c5 := hc 5 (by simp)
  have c6 := hc 6 (by simp)
  have c7 := hc 7 (by simp)
  have c8 := hc 8 (by simp)
  have c9 := hc 9 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c5 c6 c7 c8 c9
  have hne : CodeAt code (after a 10) [.subsImm 31 0 16, .bcond 1 f73] :=
    (CodeAt.split code (l1 := [.movz 0 0 0, .addImm 1 19 0, .movz 8 113 0, .bl c20, .cbnz 0 f72,
      .addImm 0 19 16, .movz 1 16 0, .movz 2 0 0, .movz 8 278 0, .bl c26]) hc rfl).2
  -- the clock
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ := run_movz P code (d := 0) (v := 0) (by decide)
    (by rw [hpc]; exact c0)
  have p1' : t1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨t2, r2, p2, x12, k2, sp2, mem2, io2⟩ := run_setX P code (d := 1) (v := t1.x 19 +
    UInt64.ofNat 0) (by decide) (by rw [p1']; exact c1)
    (exec_addImm_x P (d := 1) (n := 19) (imm := 0) (by decide) (by decide))
  have p2' : t2.pc = after a 2 := by rw [p2, p1', ← after_succ]
  obtain ⟨t3, r3, p3, x83, k3, sp3, mem3, io3⟩ := run_movz P code (d := 8) (v := 113) (by decide)
    (by rw [p2']; exact c2)
  have p3' : t3.pc = after a 3 := by rw [p3, p2', ← after_succ]
  have hmem3 : t3.mem = q.core.mem := by rw [mem3, mem2, mem1]
  have hx0 : t3.x 0 = 0 := by rw [k3 0 (by decide), k2 0 (by decide), x01]; rfl
  have hx1 : t3.x 1 = B := by
    rw [k3 1 (by decide), x12, k1 19 (by decide), h19, add_ofNat_zero]
  have hk3 : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 8 → t3.x r = q.core.x r :=
    fun r h0 h1 h8 => by rw [k3 r h8, k2 r h1, k1 r h0]
  have q1 : ProcReachWith LeanExe.Linux.table R P code q { q with core := t3 } :=
    ProcReachWith.of_reach' hdom hf (r1.trans (r2.trans r3)) (by rw [p3']; exact hdom _ _ c3)
  have hmapB : ∀ j < inMax.toNat + 33, P.normal (B + UInt64.ofNat j) = true := fun j hj => by
    rw [hBj]
    exact hst.mapped hN j hj
  have hsys := sysCall_clockGettime (R := R) (P := P) (p := ({ q with core := t3 } : Proc).call
    (after a 3) svc) (by
      rw [Proc.call_x _ _ _ (by decide)]
      show P.mapped (t3.x 1) 16 = true
      rw [hx1]
      exact mapped_of_all P fun i hi => hmapB i (by omega))
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide), Proc.call_mem] at hsys
  change sysCall R P _ _ = some (Proc.ret _ _ (writeList t3.mem (t3.x 1) _)
    (.sys ⟨_, [t3.x 0, t3.x 1], [], readList t3.mem (t3.x 1) 16, _, _⟩)) at hsys
  rw [hx0, hx1, hmem3] at hsys
  obtain ⟨q2, rq2, pq2, x0q2, -, kq2, spq2, memq2, ioq2, fq2, trq2⟩ := run_callSvc hsvc c3 hc20
    hdom (by rw [after_after]; exact hdom _ _ c4) (p := { q with core := t3 }) p3'
    (by show _ = _; rw [x83]; exact table_clock) rfl hsys
  generalize hRc : R (({ q with core := t3 } : Proc).call (after a 3) svc).trace.length = Rc
    at x0q2 memq2 trq2
  have fq2' : q2.fpcr = fpcrValue := by rw [fq2]; exact hf
  have hio2 : q2.core.io = q.core.io := by rw [ioq2]; show t3.io = _; rw [io3, io2, io1]
  have pq2' : q2.core.pc = after a 4 := by rw [pq2, after_after]
  have hev1 : sysEvents q2.trace = [⟨LeanExe.Linux.clockGettimeCall, [0, B], [],
      readList q.core.mem B 16, Rc.ret, (List.range 16).map Rc.bytes⟩] := by
    rw [trq2, sysEvents_snoc]
    show sysEvents q.trace ++ _ = _
    rw [htr]
    rfl
  by_cases hc0 : Rc.ret = 0
  swap
  · -- the clock failed: the stub of status 72
    have r4 := cbnz_taken P code (by rw [pq2']; exact c4) pq2' hf72 (by rw [x0q2]; exact hc0)
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs72 hx72 hdom hbase (q := { q2 with core := { q2.core with pc := e72 } }) rfl fq2'
    refine .inl ⟨q', q1.trans (rq2.trans ((ProcReachWith.of_reach' hdom fq2' r4 ?_).trans rq')),
      by rw [ioq']; exact hio2, pq', ?_⟩
    · have := hs72 0 (by simp [movImm])
      rw [after_zero] at this
      exact hdom _ _ this
    · rw [xq', trq']
      show StampEvents _ _ _ _ _ _ _ (sysEvents q2.trace)
      rw [hev1]
      exact StampEvents.clock hB' rfl rfl hc0

  -- the clock's bytes in the block
  have hclk : ((List.range 16).map Rc.bytes).length = 16 := by simp
  have h17q2 : q2.core.x 17 = q.core.x 17 := by
    rw [kq2 17 (by decide) (by decide)]
    exact hk3 17 (by decide) (by decide) (by decide)
  have h18q2 : q2.core.x 18 = q.core.x 18 := by
    rw [kq2 18 (by decide) (by decide)]
    exact hk3 18 (by decide) (by decide) (by decide)
  have hmB : ∀ m : UInt64 → UInt8, ∀ bs, writeList m B bs =
      writeList m (q.core.x 17 + UInt64.ofNat (4096 + (root + ([] : List UInt8).length))) bs :=
    fun m bs => by rw [List.length_nil, ← hBj 0, add_ofNat_zero]
  have hst1 := hst.write hN (O := (List.range 16).map Rc.bytes) (by simp) h17q2 h18q2
    (by rw [memq2, hmB]) (r := 16) (by simp)
  rw [List.nil_append, List.take_of_length_le (by simp)] at hst1
  have hfr1 : ∀ b : UInt64, (q.core.x 18).toNat ≤ b.toNat → q2.core.mem b = q.core.mem b :=
    fun b hb => by
      rw [memq2, hmB]
      exact hst.frame hN (O := (List.range 16).map Rc.bytes) (by simp) b hb
  -- the random bytes
  let u0 : State := { q2.core with pc := q2.core.pc + 4 }
  have r40 : Reach P code q2.core u0 := reach_exec P code (by rw [pq2']; exact c4)
    (cbnz_next P (by rw [x0q2]; exact hc0)) (.refl _)
  have pu0 : u0.pc = after a 5 := by show q2.core.pc + 4 = _; rw [pq2', ← after_succ]
  have hu19 : u0.x 19 = B := by
    show q2.core.x 19 = B
    rw [kq2 19 (by decide) (by decide), hk3 19 (by decide) (by decide) (by decide), h19]
  obtain ⟨t4, r4, p4, x04, k4, sp4, mem4, io4⟩ := run_setX P code (d := 0) (v := u0.x 19 +
    UInt64.ofNat 16) (by decide) (by rw [pu0]; exact c5)
    (exec_addImm_x P (d := 0) (n := 19) (imm := 16) (by decide) (by decide))
  have p4' : t4.pc = after a 6 := by rw [p4, pu0, ← after_succ]
  obtain ⟨t5, r5, p5, x15, k5, sp5, mem5, io5⟩ := run_movz P code (d := 1) (v := 16) (by decide)
    (by rw [p4']; exact c6)
  have p5' : t5.pc = after a 7 := by rw [p5, p4', ← after_succ]
  obtain ⟨t6, r6, p6, x26, k6, sp6, mem6, io6⟩ := run_movz P code (d := 2) (v := 0) (by decide)
    (by rw [p5']; exact c7)
  have p6' : t6.pc = after a 8 := by rw [p6, p5', ← after_succ]
  obtain ⟨t7, r7, p7, x87, k7, sp7, mem7, io7⟩ := run_movz P code (d := 8) (v := 278) (by decide)
    (by rw [p6']; exact c8)
  have p7' : t7.pc = after a 9 := by rw [p7, p6', ← after_succ]
  have hmem7 : t7.mem = q2.core.mem := by rw [mem7, mem6, mem5, mem4]
  have hx07 : t7.x 0 = B + 16 := by
    rw [k7 0 (by decide), k6 0 (by decide), k5 0 (by decide), x04, hu19]
    rfl
  have hx17 : t7.x 1 = 16 := by rw [k7 1 (by decide), k6 1 (by decide), x15]; rfl
  have hx27 : t7.x 2 = 0 := by rw [k7 2 (by decide), x26]; rfl
  have hk7 : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 8 → t7.x r = q2.core.x r :=
    fun r h0 h1 h2 h8 => by rw [k7 r h8, k6 r h2, k5 r h1, k4 r h0]; rfl
  have q3 : ProcReachWith LeanExe.Linux.table R P code q2 { q2 with core := t7 } :=
    ProcReachWith.of_reach' hdom fq2' (r40.trans (r4.trans (r5.trans (r6.trans r7))))
      (by rw [p7']; exact hdom _ _ c9)
  have hsys2 := sysCall_getrandom (R := R) (P := P) (p := ({ q2 with core := t7 } : Proc).call
    (after a 9) svc) (by
      rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide)]
      show P.mapped (t7.x 0) (t7.x 1).toNat = true
      rw [hx07, hx17]
      exact mapped_of_all P fun i hi => by
        rw [show B + 16 + UInt64.ofNat i = B + UInt64.ofNat (16 + i) by
          rw [show (16 : UInt64) = UInt64.ofNat 16 from rfl, add_ofNat_add]]
        exact hmapB _ (by simp at hi; omega))
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_mem] at hsys2
  change sysCall R P _ _ = some (Proc.ret _ _ (writeList t7.mem (t7.x 0) _)
    (.sys ⟨_, [t7.x 0, t7.x 1, t7.x 2], [], readList t7.mem (t7.x 0) (t7.x 1).toNat, _,
      (List.range (t7.x 1).toNat).map _⟩)) at hsys2
  rw [hx07, hx17, hx27, hmem7, show (16 : UInt64).toNat = 16 from rfl] at hsys2
  obtain ⟨q4, rq4, pq4, x0q4, -, kq4, spq4, memq4, ioq4, fq4, trq4⟩ := run_callSvc hsvc c9 hc26
    hdom (by rw [after_after]; exact hdom _ _ (by simpa [after_zero] using hne 0 (by simp)))
    (p := { q2 with core := t7 }) p7' (by show _ = _; rw [x87]; exact table_random) rfl hsys2
  generalize hRr : R (({ q2 with core := t7 } : Proc).call (after a 9) svc).trace.length = Rr
    at x0q4 memq4 trq4
  have fq4' : q4.fpcr = fpcrValue := by rw [fq4]; exact fq2'
  have hio4 : q4.core.io = q.core.io := by
    rw [ioq4]; show t7.io = _; rw [io7, io6, io5, io4]; exact hio2
  have pq4' : q4.core.pc = after a 10 := by rw [pq4, after_after]
  have hev2 : sysEvents q4.trace = [⟨LeanExe.Linux.clockGettimeCall, [0, B], [],
      readList q.core.mem B 16, Rc.ret, (List.range 16).map Rc.bytes⟩,
      ⟨LeanExe.Linux.getrandomCall, [B + 16, 16, 0], [], readList q2.core.mem (B + 16) 16, Rr.ret,
        (List.range 16).map Rr.bytes⟩] := by
    rw [trq4, sysEvents_snoc]
    show sysEvents q2.trace ++ _ = _
    rw [hev1]
    rfl
  obtain ⟨u1, ru1, pu1, xu1, spu1, memu1, iou1⟩ := run_ne16 (P := P) (code := code) hne
    (by rw [after_after]; exact hf73) pq4'
  by_cases hr16 : Rr.ret = 16
  swap
  · -- the random bytes failed: the stub of status 73
    rw [x0q4, ite_eq_right hr16] at pu1
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs73 hx73 hdom hbase (q := { q4 with core := u1 }) pu1 fq4'
    refine .inl ⟨q', q1.trans (rq2.trans (q3.trans (rq4.trans
      ((ProcReachWith.of_reach' hdom fq4' ru1 ?_).trans rq')))), ?_, pq', ?_⟩
    · rw [pu1]
      have := hs73 0 (by simp [movImm])
      rw [after_zero] at this
      exact hdom _ _ this
    · rw [ioq']
      show u1.io = _
      rw [iou1, hio4]
    · rw [xq', trq']
      show StampEvents _ _ _ _ _ _ _ (sysEvents q4.trace)
      rw [hev2]
      exact StampEvents.random hB' rfl rfl hc0 rfl rfl hr16
  rw [x0q4, ite_eq_left hr16] at pu1
  -- the random bytes in the block
  have h17q4 : q4.core.x 17 = q2.core.x 17 := by
    rw [kq4 17 (by decide) (by decide)]
    exact hk7 17 (by decide) (by decide) (by decide) (by decide)
  have h18q4 : q4.core.x 18 = q2.core.x 18 := by
    rw [kq4 18 (by decide) (by decide)]
    exact hk7 18 (by decide) (by decide) (by decide) (by decide)
  have hmB16 : B + 16 = q2.core.x 17 + UInt64.ofNat (4096 + (root +
      ((List.range 16).map Rc.bytes).length)) := by
    rw [hclk, h17q2, ← hBj 16]
    rfl
  have hst2 := hst1.write hN (O := (List.range 16).map Rr.bytes)
    (by simp only [List.length_map, List.length_range]; omega) h17q4 h18q4
    (by rw [memq4, hmB16]) (r := 16) (by simp)
  rw [List.take_of_length_le (by simp)] at hst2
  have hfr2 : ∀ b : UInt64, (q2.core.x 18).toNat ≤ b.toNat → q4.core.mem b = q2.core.mem b :=
    fun b hb => by
      rw [memq4, hmB16]
      exact hst1.frame hN (O := (List.range 16).map Rr.bytes)
        (by simp only [List.length_map, List.length_range]; omega) b hb
  -- the stores of the input path
  have hsp4 : q4.core.sp = SPf := by
    rw [spq4]; show t7.sp = _; rw [sp7, sp6, sp5, sp4]; show q2.core.sp = _
    rw [spq2]; show t3.sp = _; rw [sp3, sp2, sp1, hsp]
  have hcs := storeWords_code hsIn hcIn
  have hpu1 : u1.pc = after (after a 12) 0 := by rw [pu1, after_zero, after_after]
  obtain ⟨t8, r8, p8, sp8, io8, k8, hin8, hout8⟩ := run_storeWords (P := P) (code := code)
    (pathWords pin) 4 (s := u1) (by simpa using hcs)
    (by rw [hpu1, after_zero]) (by rw [spu1, hsp4]; exact hal)
    (by rw [spu1, hsp4]; exact htop)
    (fun j hj => by rw [spu1, hsp4]; exact hframe j (by omega))
  rw [spu1, hsp4] at hin8 hout8
  have p8' : t8.pc = after a (12 + 5 * (pathWords pin).length) := by rw [p8, after_after]
  have hsp8 : t8.sp = SPf := by rw [sp8, spu1, hsp4]
  -- the open of the input
  have hpath : ∀ j ≤ pin.length,
      t8.mem (t8.sp + UInt64.ofNat (32 : Fin 4096).val + UInt64.ofNat j) = pin.getD j 0 := by
    intro j hj
    rw [hsp8, show SPf + UInt64.ofNat (32 : Fin 4096).val = slotAddr SPf 4 from rfl,
      hin8 j (by omega), pathWords_byte pin (by omega)]
  have hpm : ∀ j ≤ pin.length,
      P.normal (t8.sp + UInt64.ofNat (32 : Fin 4096).val + UInt64.ofNat j) = true := by
    intro j hj
    rw [hsp8, add_ofNat_add]
    exact hframe _ (by have : (32 : Fin 4096).val = 32 := rfl; omega)
  have fq4u : ({ q4 with core := t8 } : Proc).fpcr = fpcrValue := fq4'
  obtain ⟨q5, ev, rq5, fq5, ioq5, trq5, hev1o, hev2o, hev3o, hout⟩ := run_open (T := LeanExe.Linux.table)
    (R := R) (P := P) (code := code) (o := after a (12 + 5 * (pathWords pin).length))
    hco hcI hf67 hsvc table_openat hdom (by
      rw [after_after, show 12 + 5 * (pathWords pin).length + 15 =
        27 + 5 * (pathWords pin).length by omega]
      exact hdom _ _ (by simpa [after_zero] using hco2 0 (by simp)))
    (by
      have := hs67 0 (by simp [movImm])
      rw [after_zero] at this
      exact hdom _ _ this) (by omega) hnz (q := { q4 with core := t8 }) p8' fq4u
    (by show t8.sp % 16 = 0; rw [hsp8]; exact hal)
    (fun j hj => by show P.normal (t8.sp + _) = true; rw [hsp8]; exact hframe j (by omega))
    hpath hpm
  have r48 : ProcReachWith LeanExe.Linux.table R P code q4 { q4 with core := t8 } :=
    ProcReachWith.of_reach' hdom fq4' (ru1.trans r8) (by rw [p8']; exact hdom _ _ (by
      simpa [after_zero] using hco 0 (by simp [movImm])))
  have hreach : ProcReachWith LeanExe.Linux.table R P code q q5 :=
    q1.trans (rq2.trans (q3.trans (rq4.trans (r48.trans rq5))))
  have hev3 : sysEvents q5.trace = [⟨LeanExe.Linux.clockGettimeCall, [0, B], [],
      readList q.core.mem B 16, Rc.ret, (List.range 16).map Rc.bytes⟩,
      ⟨LeanExe.Linux.getrandomCall, [B + 16, 16, 0], [], readList q2.core.mem (B + 16) 16, Rr.ret,
        (List.range 16).map Rr.bytes⟩, ev] := by
    rw [trq5, sysEvents_snoc]
    show sysEvents q4.trace ++ _ = _
    rw [hev2]
    rfl
  have hargs : ev.args = [atFdcwd, sp0 - UInt64.ofNat (stampFrame pin pout) + 32, stampInFlags,
      0] := by
    rw [hev2o, hSPf]
    show [atFdcwd, t8.sp + _, stampInFlags, _] = _
    rw [hsp8]
    rfl
  rcases hout with ⟨hbig, pq5⟩ | ⟨hsmall, pq5, spq5, memq5, kq5⟩
  · -- the open failed: the stub of status 67
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs67 hx67 hdom hbase (q := q5) pq5 fq5
    refine .inl ⟨q', hreach.trans rq', ?_, pq', ?_⟩
    · rw [ioq', ioq5]
      show t8.io = _
      rw [io8, iou1, hio4]
    · rw [xq', trq', hev3]
      exact StampEvents.openIn hB' rfl rfl hc0 rfl rfl hr16 hev1o hargs hev3o hbig
  -- the block's address and the count
  have hc2' := CodeAt.split code hco2 (l1 := [.addImm 1 19 32]) (n := 1) rfl
  have ca : code (after a (27 + 5 * (pathWords pin).length)) = some (encode (.addImm 1 19 32)) :=
    (CodeAt.cons.mp hc2'.1).1
  have pq5' : q5.core.pc = after a (27 + 5 * (pathWords pin).length) := by
    rw [pq5, after_after]
    congr 1
    omega
  obtain ⟨t9, r9, p9, x19', k9, sp9, mem9, io9⟩ := run_setX P code (d := 1)
    (v := q5.core.x 19 + UInt64.ofNat 32) (by decide) (by rw [pq5']; exact ca)
    (exec_addImm_x P (d := 1) (n := 19) (imm := 32) (by decide) (by decide))
  obtain ⟨t10, r10, p10, x210, k10, sp10, mem10, io10⟩ := run_movImm P code (d := 2)
    (v := inMax + 1) (by decide) hc2'.2 (by rw [p9, pq5', ← after_succ, after_after])
  have p10' : t10.pc = after a (32 + 5 * (pathWords pin).length) := by
    rw [p10, after_after, after_after]
    congr 1
    omega
  have hq5x19 : q5.core.x 19 = B := by
    rw [kq5 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    show t8.x 19 = _
    rw [k8 19 (by decide)]
    show u1.x 19 = _
    rw [xu1 19, kq4 19 (by decide) (by decide), hk7 19 (by decide) (by decide) (by decide)
      (by decide)]
    exact hu19
  have hreach' : ProcReachWith LeanExe.Linux.table R P code q { q5 with core := t10 } :=
    hreach.trans (ProcReachWith.of_reach' hdom fq5 (r9.trans r10) (by rw [p10']; exact hend))
  -- the memory: the frame's slots and the block
  have hmem10 : t10.mem = store64 t8.mem (slotAddr SPf 2) ev.ret := by
    rw [mem10, mem9, memq5]
    show store64 t8.mem (slotAddr t8.sp 2) ev.ret = _
    rw [hsp8]
  have hx18 : ∀ s : State, s.x 18 = q.core.x 18 → (s.x 18).toNat ≤ SPf.toNat := fun s h => by
    rw [h]; exact h18
  have h18q4' : q4.core.x 18 = q.core.x 18 := by rw [h18q4, h18q2]
  have h17q4' : q4.core.x 17 = q.core.x 17 := by rw [h17q4, h17q2]
  -- bytes below the stack's limit keep their values from `q4` on
  have hlow : ∀ b : UInt64, b.toNat < (q.core.x 18).toNat → t10.mem b = q4.core.mem b := by
    intro b hb
    rw [hmem10, store64_other _ _ _ _ (below_slot (lim := q.core.x 18) h18 htop (by decide) hb),
      hout8 b ?_, memu1]
    have hXe := toNat_slot SPf 4
    have hbt := b.toNat_lt
    rw [UInt64.toNat_sub, hXe]
    simp only [Nat.reducePow] at *
    omega
  -- the slots 0 and 1 keep their values
  have hslot : ∀ i < 2, load64 t10.mem (slotAddr SPf i) = load64 q.core.mem (slotAddr SPf i) := by
    intro i hi
    apply load64_congr
    intro k hk
    rw [hmem10, store64_other _ _ _ _
      (slot_apart (sp := SPf) (i := 2) (j := i) (by decide) (by omega) (by omega) k hk),
      hout8 _ (below_slots (by omega) (by omega) k hk), memu1, hfr2 _ ?_, hfr1 _ ?_]
    · have := slot_le (sp := SPf) (i := i) htop (by omega) hk
      omega
    · have := slot_le (sp := SPf) (i := i) htop (by omega) hk
      rw [h18q2]
      omega
  refine .inr ⟨{ q5 with core := t10 }, ⟨LeanExe.Linux.clockGettimeCall, [0, B], [],
      readList q.core.mem B 16, Rc.ret, (List.range 16).map Rc.bytes⟩,
    ⟨LeanExe.Linux.getrandomCall, [B + 16, 16, 0], [], readList q2.core.mem (B + 16) 16, Rr.ret,
      (List.range 16).map Rr.bytes⟩, ev, hreach', fq5, ?_,
    ⟨hB', rfl, rfl, hc0, rfl, rfl, hr16, hev1o, hargs, hev3o, hsmall⟩, by simp, by simp,
    hev3, p10', ?_, ?_, ?_, ?_, ?_, ?_, hslot, ?_⟩
  · show t10.io = _
    rw [io10, io9, ioq5]
    show t8.io = _
    rw [io8, iou1, hio4]
  · show t10.sp = _
    rw [sp10, sp9, spq5, hsp8, hsp]
  · show t10.x 17 = _
    rw [k10 17 (by decide), k9 17 (by decide), kq5 17 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    show t8.x 17 = _
    rw [k8 17 (by decide)]
    show u1.x 17 = _
    rw [xu1 17, h17q4', h17]
  · show t10.x 18 = _
    rw [k10 18 (by decide), k9 18 (by decide), kq5 18 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    show t8.x 18 = _
    rw [k8 18 (by decide)]
    show u1.x 18 = _
    rw [xu1 18, h18q4']
  · show t10.x 1 = _
    rw [k10 1 (by decide), x19', hq5x19, ← hBdef, block_addr]
  · show t10.x 2 = _
    rw [x210]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    rfl
  · show load64 t10.mem _ = _
    rw [hmem10, load64_store64_same]
  · obtain ⟨st', hsr, hW, hD⟩ := hst2
    refine ⟨st', hsr.congr ?_ ?_ fun b hb => ?_, hW, hD⟩
    · show t10.x 17 = _
      rw [k10 17 (by decide), k9 17 (by decide), kq5 17 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      show t8.x 17 = _
      rw [k8 17 (by decide)]
      show u1.x 17 = _
      rw [xu1 17]
    · show t10.x 18 = _
      rw [k10 18 (by decide), k9 18 (by decide), kq5 18 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      show t8.x 18 = _
      rw [k8 18 (by decide)]
      show u1.x 18 = _
      rw [xu1 18]
    · rw [h18q4'] at hb
      exact hlow b hb
/-! ## The read loop, the input's close, and the call of the function -/

/-- From the head of the read loop: the reads of the input's descriptor into the block, the store
of the count read in the frame's slot 3, the input's `close`, and the call of the function on the
block's root and the number of bytes that the block holds.  The run reaches the exit word with
status 68, 64, or 69, with the events of `StampEvents`; or it reaches the function's entry with
the root in X0, the count of the clock's, the random, and the input's bytes in X1, and the block
holding them. -/
theorem stamp_read {H svc e64 e68 e69 base e : UInt64}
    {cR g64 cC gk x64 x68 x69 : Fin 67108864} {fe f68 fr f69 : Fin 524288}
    {inMax sp0 SPf rootU B : UInt64} {cap : Nat} {gts : List ValueType}
    {st1 : Store Unit} {pin pout : List UInt8}
    {Out : List UInt8 → List UInt8} {Tr : List UInt8 → UInt64 → Prop}
    (hc : CodeAt code H [.ldr 0 31 2, .movz 8 63 0, .bl cR, .cbz 0 fe, .subsReg 31 0 2,
      .bcond 8 f68, .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b g64])
    (hcR : bField (after H 2) svc = .ok cR) (hfe : cbField (after H 3) (after H 10) = .ok fe)
    (hf68 : cbField (after H 5) e68 = .ok f68) (hfr : cbField (after H 8) H = .ok fr)
    (hg64 : bField (after H 9) e64 = .ok g64)
    (hca : CodeAt code (after H 10) (movImm 16 (inMax + 1) ++ [.subReg 16 16 2, .str 16 31 3,
      .ldr 0 31 2, .movz 8 57 0, .bl cC, .cbnz 0 f69, .ldr 0 31 1, .ldr 1 31 3, .addImm 1 1 32,
      .bl gk]))
    (hcC : bField (after H 18) svc = .ok cC) (hf69 : cbField (after H 19) e69 = .ok f69)
    (hgk : bField (after H 23) e = .ok gk)
    (hs64 : CodeAt code e64 (movImm 0 (UInt64.ofNat 64) ++ [.b x64]))
    (hx64 : bField (after e64 4) base = .ok x64)
    (hs68 : CodeAt code e68 (movImm 0 (UInt64.ofNat 68) ++ [.b x68]))
    (hx68 : bField (after e68 4) base = .ok x68)
    (hs69 : CodeAt code e69 (movImm 0 (UInt64.ofNat 69) ++ [.b x69]))
    (hx69 : bField (after e69 4) base = .ok x69)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (hbase : base.toNat < 2 ^ 55)
    (he : e.toNat < 2 ^ 55) (h10 : (after H 10).toNat < 2 ^ 55) (hin : inMax.toNat < 2 ^ 32)
    {q : Proc} {ec er eo : LeanExe.Linux.Event} (hpc : q.core.pc = H) (hf : q.fpcr = fpcrValue)
    (hop : StampOpened sp0 inMax pin pout B ec er eo)
    (hl16 : ec.output.length = 16) (hr16 : er.output.length = 16)
    (htr : sysEvents q.trace = [ec, er, eo])
    (hsp : q.core.sp = SPf) (hal : SPf % 16 = 0) (htop : SPf.toNat < 2 ^ 63)
    (hframe : ∀ j < 32, P.normal (SPf + UInt64.ofNat j) = true)
    (h18 : (q.core.x 18).toNat ≤ SPf.toNat)
    (h1 : q.core.x 1 = q.core.x 17 + UInt64.ofNat (4096 + (rootU.toNat + 32)))
    (h1B : q.core.x 1 = B + 32)
    (h2 : q.core.x 2 = UInt64.ofNat (inMax.toNat + 1))
    (hs1 : load64 q.core.mem (slotAddr SPf 1) = rootU)
    (hs2 : load64 q.core.mem (slotAddr SPf 2) = eo.ret)
    (hst : ReadStore P cap gts st1 rootU.toNat (inMax.toNat + 33) (ec.output ++ er.output) q.core)
    (hN : rootU.toNat + (inMax.toNat + 33) ≤ st1.mem.pages * 65536) :
    (∃ q', ProcReachWith LeanExe.Linux.table R P code q q' ∧ q'.core.io = q.core.io ∧
      q'.core.pc = base ∧
      StampEvents sp0 inMax pin pout Out Tr (some (q'.core.x 0)) (sysEvents q'.trace)) ∨
    (∃ q' rs ecl, ProcReachWith LeanExe.Linux.table R P code q q' ∧ q'.fpcr = fpcrValue ∧
      q'.core.io = q.core.io ∧ StampInput sp0 inMax pin pout B ec er eo rs ecl ∧
      (readData eo.ret rs).length ≤ inMax.toNat ∧
      sysEvents q'.trace = [ec, er, eo] ++ rs ++ [ecl] ∧
      q'.core.pc = e ∧ q'.core.x 30 = after H 24 ∧ q'.core.x 0 = rootU ∧
      q'.core.x 1 = UInt64.ofNat (ec.output ++ er.output ++ readData eo.ret rs).length ∧
      q'.core.sp = SPf ∧ q'.core.x 17 = q.core.x 17 ∧ q'.core.x 18 = q.core.x 18 ∧
      load64 q'.core.mem (slotAddr SPf 0) = load64 q.core.mem (slotAddr SPf 0) ∧
      ReadStore P cap gts st1 rootU.toNat (inMax.toNat + 33)
        (ec.output ++ er.output ++ readData eo.ret rs) q'.core) := by
  have hd0 : readData eo.ret (sysEvents q.trace) = [] := by
    rw [htr, show [ec, er, eo] = [ec, er, eo] ++ [] from rfl, readData_stamp hop]
    rfl
  have hpre : (ec.output ++ er.output).length = 32 := by
    rw [List.length_append, hl16, hr16]
  have hstub : ∀ (c : Nat) (a : UInt64) (g : Fin 67108864),
      CodeAt code a (movImm 0 (UInt64.ofNat c) ++ [.b g]) → bField (after a 4) base = .ok g →
      (a.toNat < 2 ^ 55) := fun c a g hca _ => by
    have := hca 0 (by simp [movImm])
    rw [after_zero] at this
    exact hdom _ _ this
  obtain ⟨p1, rs, rp1, fp1, iop1, trp1, res⟩ := run_stampReadLoop (T := LeanExe.Linux.table)
    (R := R) (P := P) (code := code) hc hcR hfe hf68 hfr hg64 hsvc table_read hdom h10
    (hstub _ _ _ hs64 hx64) (hstub _ _ _ hs68 hx68) st1 rootU.toNat (inMax.toNat + 33) hN
    (ec.output ++ er.output) eo.ret SPf hal htop (fun j hj => hframe j (by omega))
    (inMax.toNat + 1) q (by rw [hd0, List.append_nil, hpre]; omega) (by omega) hpc hf h2
    (by rw [hd0, List.append_nil, hpre]; exact h1) hsp h18 hs2 (by rw [hd0, List.append_nil]; exact hst)
  rw [h1B] at res
  have hrs : ∀ tr : List Event, sysEvents tr = sysEvents q.trace ++ rs →
      readData eo.ret (sysEvents tr) = readData eo.ret rs := fun tr h => by
    rw [h, readData_append, hd0, List.nil_append]
  rcases res with ⟨pc1, hrl⟩ | ⟨pc1, hrl, hlen⟩ | ⟨pc1, hrl, hlt, hx2, hst1, hk1, hsp1, hfr1⟩
  · -- a read above its count: the stub of status 68
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs68 hx68 hdom hbase pc1 fp1
    refine .inl ⟨q', rp1.trans rq', by rw [ioq', iop1], pq', ?_⟩
    rw [xq', trq', trp1, htr]
    exact StampEvents.read68 hop hrl
  · -- the block is full: the stub of status 64
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs64 hx64 hdom hbase pc1 fp1
    refine .inl ⟨q', rp1.trans rq', by rw [ioq', iop1], pq', ?_⟩
    rw [xq', trq', trp1, htr]
    refine StampEvents.read64 hop hrl ?_
    rw [hrs _ trp1, List.length_append, hpre] at hlen
    omega
  -- the end of the input
  rw [hrs _ trp1] at hlt hx2 hst1
  rw [List.length_append, hpre] at hlt hx2
  generalize hn : (readData eo.ret rs).length = n at hlt hx2
  have hsp1' : p1.core.sp = SPf := by rw [hsp1, hsp]
  -- the count into the frame's slot 3
  have sa := CodeAt.split code hca (n := 4) (movImm_length _ _)
  obtain ⟨t1, r1, pt1, x16t1, kt1, spt1, memt1, iot1⟩ :=
    run_movImm P code (d := 16) (v := inMax + 1) (by decide) sa.1 pc1
  have ca5 := (CodeAt.cons.mp sa.2).1
  have ca6 := (CodeAt.cons.mp (CodeAt.cons.mp sa.2).2).1
  have hsplit := CodeAt.split code (CodeAt.cons.mp (CodeAt.cons.mp sa.2).2).2
    (l1 := [.ldr 0 31 2, .movz 8 57 0, .bl cC, .cbnz 0 f69]) (n := 4) rfl
  simp only [after_after, Nat.reduceAdd] at ca5 ca6 hsplit pt1
  have hcl := hsplit.1
  have hcr := hsplit.2
  obtain ⟨t2, r2, pt2, x16t2, kt2, spt2, memt2, iot2⟩ := run_setX P code (d := 16)
    (v := t1.x 16 - t1.x 2) (by decide) (by rw [pt1]; exact ca5)
    (rfl : exec P (.subReg 16 16 2) t1 = _)
  have hspt2 : t2.sp = SPf := by rw [spt2, spt1, hsp1']
  have pt2' : t2.pc = after H 15 := by rw [pt2, pt1, ← after_succ]
  let t3 : State := { t2 with mem := store64 t2.mem (slotAddr t2.sp 3) (t2.x 16), pc := t2.pc + 4 }
  have e3 : exec P (.str 16 31 3) t2 = some t3 :=
    exec_str_sp P (i := 3) (by decide) (by rw [hspt2]; exact hal)
      fun j hj => by rw [hspt2]; exact hframe _ (by omega)
  have r3 : Reach P code p1.core t3 := r1.trans (r2.trans (reach_exec P code
    (by rw [pt2']; exact ca6) e3 (.refl _)))
  have pt3 : t3.pc = after H 16 := by
    show t2.pc + 4 = _
    rw [pt2', ← after_succ]
  have hx16 : t2.x 16 = UInt64.ofNat n := by
    rw [x16t2, x16t1, kt1 2 (by decide), hx2]
    rw [show inMax + 1 = UInt64.ofNat (inMax.toNat + 1) by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      rfl]
    rw [ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
    omega
  have q3 : ProcReachWith LeanExe.Linux.table R P code p1 { p1 with core := t3 } :=
    ProcReachWith.of_reach' hdom fp1 r3 (by rw [pt3]; exact hdom _ _ (by
      simpa [after_zero] using hcl 0 (by simp)))
  have hst3 : load64 t3.mem (slotAddr SPf 2) = eo.ret := by
    show load64 (store64 t2.mem (slotAddr t2.sp 3) (t2.x 16)) _ = _
    rw [hspt2, load64_store64_other _ _ _ _
      (slot_apart (sp := SPf) (i := 3) (j := 2) (by decide) (by decide) (by decide)),
      memt2, memt1, load64_congr (m' := q.core.mem) fun k hk => hfr1 _ (by
        have := slot_le (sp := SPf) (i := 2) htop (by decide) hk
        omega), hs2]
  -- the input's close
  obtain ⟨p4, ecl, rp4, fp4, iop4, trp4, hcl1, hcl2, res4⟩ := run_close (T := LeanExe.Linux.table)
    (R := R) (P := P) (code := code) hcl (by simp only [after_after]; exact hcC)
    (by simp only [after_after]; exact hf69) hsvc table_close hdom
    (by simp only [after_after]; exact hdom _ _ (by simpa [after_zero] using hcr 0 (by simp)))
    (hstub _ _ _ hs69 hx69) (q := { p1 with core := t3 }) pt3 fp1
    (by show t3.sp % 16 = 0; rw [show t3.sp = SPf from hspt2]; exact hal)
    (fun j hj => by show P.normal (t3.sp + _) = true; rw [show t3.sp = SPf from hspt2]
                    exact hframe j (by omega))
  rw [show ({ p1 with core := t3 } : Proc).core.mem = t3.mem from rfl,
    show ({ p1 with core := t3 } : Proc).core.sp = SPf from hspt2, hst3] at hcl2
  have htr4 : sysEvents p4.trace = [ec, er, eo] ++ rs ++ [ecl] := by
    rw [trp4, sysEvents_snoc]
    show sysEvents p1.trace ++ _ = _
    rw [trp1, htr]
  have hlen : (readData eo.ret rs).length ≤ inMax.toNat := by omega
  rcases res4 with ⟨hne, pc4⟩ | ⟨h0, pc4, sp4, mem4, k4⟩
  · obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs69 hx69 hdom hbase pc4 fp4
    refine .inl ⟨q', rp1.trans (q3.trans (rp4.trans rq')), ?_, pq', ?_⟩
    · rw [ioq', iop4]
      show t3.io = _
      rw [iot2, iot1, iop1]
    · rw [xq', trq', htr4]
      exact StampEvents.close69 hop hrl hlen hcl1 hcl2 hne

  -- the root and the count into X0 and X1, and the call of the function
  have c0 := hcr 0 (by simp)
  have c1 := hcr 1 (by simp)
  have c2 := hcr 2 (by simp)
  have c3 := hcr 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, Nat.reduceAdd] at c0 c1
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, Nat.reduceAdd] at c2 c3
  simp only [after_after, Nat.reduceAdd] at pc4
  have hsp4 : p4.core.sp = SPf := by rw [sp4]; exact hspt2
  have hmem4 : p4.core.mem = t3.mem := mem4
  have hs1' : load64 p4.core.mem (slotAddr SPf 1) = rootU := by
    rw [hmem4]
    show load64 (store64 t2.mem (slotAddr t2.sp 3) (t2.x 16)) _ = _
    rw [hspt2, load64_store64_other _ _ _ _
      (slot_apart (sp := SPf) (i := 3) (j := 1) (by decide) (by decide) (by decide)),
      memt2, memt1, load64_congr (m' := q.core.mem) fun k hk => hfr1 _ (by
        have := slot_le (sp := SPf) (i := 1) htop (by decide) hk
        omega), hs1]
  have hs3' : load64 p4.core.mem (slotAddr SPf 3) = UInt64.ofNat n := by
    rw [hmem4]
    show load64 (store64 t2.mem (slotAddr t2.sp 3) (t2.x 16)) _ = _
    rw [hspt2, load64_store64_same, hx16]
  obtain ⟨u1, ru1, pu1, x0u1, ku1, spu1, memu1, iou1⟩ := run_setX P code (d := 0) (by decide)
    (by rw [pc4]; exact c0) (exec_ldr_sp P (s := p4.core) (r := 0) (i := 1) _
      (by rw [hsp4]; exact hal) fun j hj => by rw [hsp4]; exact hframe _ (by omega))
  obtain ⟨u2, ru2, pu2, x1u2, ku2, spu2, memu2, iou2⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pu1, pc4, ← after_succ]; exact c1) (exec_ldr_sp P (s := u1) (r := 1) (i := 3) _
      (by rw [spu1, hsp4]; exact hal) fun j hj => by rw [spu1, hsp4]; exact hframe _ (by omega))
  have pu2' : u2.pc = after H 22 := by rw [pu2, pu1, pc4, ← after_succ, ← after_succ]
  obtain ⟨u3, ru3, pu3, x1u3, ku3, spu3, memu3, iou3⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pu2']; exact c2)
    (exec_addImm_x P (s := u2) (d := 1) (n := 1) (imm := 32) (by decide) (by decide))
  have pu3' : u3.pc = after H 23 := by rw [pu3, pu2', ← after_succ]
  let u4 : State := { u3.setX 30 (u3.pc + 4) with pc := u3.pc + sext 26 gk.val * 4 }
  have ru4 : Reach P code p4.core u4 := ru1.trans (ru2.trans (ru3.trans
    (reach_exec P code (by rw [pu3']; exact c3) rfl (.refl _))))
  have pu4 : u4.pc = e := by
    show u3.pc + sext 26 gk.val * 4 = _
    rw [pu3']
    exact bField_target hgk
  have fp4' : p4.fpcr = fpcrValue := fp4
  refine .inr ⟨{ p4 with core := u4 }, rs, ecl,
    rp1.trans (q3.trans (rp4.trans (ProcReachWith.of_reach' hdom fp4' ru4 (by rw [pu4]; exact he)))),
    fp4, ?_, ⟨hop, hrl, hcl1, hcl2, h0⟩, hlen, htr4, pu4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show u4.io = _
    show (u3.setX 30 (u3.pc + 4)).io = _
    rw [State.setX_io, iou3, iou2, iou1, iop4]
    show t3.io = _
    rw [iot2, iot1, iop1]
  · show u4.x 30 = _
    rw [State.x_withPc, State.x_setX_same (by decide), pu3', ← after_succ]
  · show u4.x 0 = _
    rw [State.x_withPc, State.x_setX_ne (by decide), ku3 0 (by decide), ku2 0 (by decide), x0u1,
      hsp4, hs1']
  · show u4.x 1 = _
    rw [State.x_withPc, State.x_setX_ne (by decide), x1u3, x1u2, spu1, hsp4, memu1, hs3',
      List.length_append, List.length_append, hl16, hr16, hn, ← UInt64.ofNat_add]
    congr 1
    have : ((32 : Fin 4096) : Nat) = 32 := rfl
    omega
  · show (u3.setX 30 (u3.pc + 4)).sp = _
    rw [State.setX_sp, spu3, spu2, spu1, hsp4]
  · show u4.x 17 = _
    rw [State.x_withPc, State.x_setX_ne (by decide), ku3 17 (by decide), ku2 17 (by decide),
      ku1 17 (by decide), k4 17 (by decide) (by decide) (by decide)]
    show t2.x 17 = _
    rw [kt2 17 (by decide), kt1 17 (by decide)]
    exact hk1 17 (by decide) (by decide) (by decide) (by decide) (by decide)
  · show u4.x 18 = _
    rw [State.x_withPc, State.x_setX_ne (by decide), ku3 18 (by decide), ku2 18 (by decide),
      ku1 18 (by decide), k4 18 (by decide) (by decide) (by decide)]
    show t2.x 18 = _
    rw [kt2 18 (by decide), kt1 18 (by decide)]
    exact hk1 18 (by decide) (by decide) (by decide) (by decide) (by decide)
  · show load64 (u3.setX 30 (u3.pc + 4)).mem _ = _
    rw [State.setX_mem, memu3, memu2, memu1, hmem4]
    show load64 (store64 t2.mem (slotAddr t2.sp 3) (t2.x 16)) _ = _
    rw [hspt2, load64_store64_other _ _ _ _
      (slot_apart (sp := SPf) (i := 3) (j := 0) (by decide) (by decide) (by decide)),
      memt2, memt1]
    exact load64_congr fun k hk => hfr1 _ (by
      have := slot_le (sp := SPf) (i := 0) htop (by decide) hk
      omega)
  · obtain ⟨st', hsr, hW, hD⟩ := hst1
    have h18p1 : p1.core.x 18 = q.core.x 18 :=
      hk1 18 (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨st', hsr.congr ?_ ?_ fun b hb => ?_, hW, hD⟩
    · show u4.x 17 = _
      rw [State.x_withPc, State.x_setX_ne (by decide), ku3 17 (by decide), ku2 17 (by decide),
        ku1 17 (by decide), k4 17 (by decide) (by decide) (by decide)]
      show t2.x 17 = _
      rw [kt2 17 (by decide), kt1 17 (by decide)]
    · show u4.x 18 = _
      rw [State.x_withPc, State.x_setX_ne (by decide), ku3 18 (by decide), ku2 18 (by decide),
        ku1 18 (by decide), k4 18 (by decide) (by decide) (by decide)]
      show t2.x 18 = _
      rw [kt2 18 (by decide), kt1 18 (by decide)]
    · show (u3.setX 30 (u3.pc + 4)).mem b = _
      rw [State.setX_mem, memu3, memu2, memu1, hmem4]
      show store64 t2.mem (slotAddr t2.sp 3) (t2.x 16) b = _
      rw [hspt2, store64_other _ _ _ _ (below_slot (lim := p1.core.x 18)
        (by rw [h18p1]; exact h18) htop (by decide) hb), memt2, memt1]

/-! ## The output -/

theorem slotAddr_eq (sp : UInt64) (i : Nat) : slotAddr sp i = sp + UInt64.ofNat (8 * i) := by
  apply UInt64.toNat_inj.mp
  rw [toNat_slot, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

/-- From the function's return with the root and the length of its result in X0 and X1: the
result's address and length into the frame's slots 1 and 3, the stores of the output path's words
into the frame, the `openat` of the output, the writes of the result, the output's `close`, and
the return.  The run reaches the exit word with status 70, 74, or 71, or returns 0 to the address
in the frame's slot 0, with the events of `StampEvents`. -/
theorem stamp_output {a svc e70 e74 e71 base : UInt64} {outSlot fr : Fin 4096}
    {cO cW gb cD x70 x74 x71 : Fin 67108864} {f70 fd fz fw f71 : Fin 524288}
    {sp0 SPf ret0 inMax : UInt64} {cap : Nat} {gts : List ValueType}
    {pin pout : List UInt8} {sOut : List Instr}
    {Out : List UInt8 → List UInt8} {Tr : List UInt8 → UInt64 → Prop}
    {B : UInt64} {ec er eo ecl : LeanExe.Linux.Event} {rs : List LeanExe.Linux.Event}
    (hc1 : CodeAt code a [mov 2 1, .addReg 1 17 0, .addImm 1 1 2048, .addImm 1 1 2048,
      .str 1 31 1, .str 2 31 3])
    (hsOut : storeWords (pathWords pout) (4 + (pathWords pin).length) = .ok sOut)
    (hcs : CodeAt code (after a 6) sOut)
    (hco : CodeAt code (after a (6 + 5 * (pathWords pout).length))
      (movImm 0 atFdcwd ++ [.addImm 1 31 outSlot] ++ movImm 2 stampOutFlags ++
        [.movz 3 stampOutMode 0, .movz 8 56 0, .bl cO, .lsrImm 16 0 31, .cbnz 16 f70,
          .str 0 31 2]))
    (hcO : bField (after (after a (6 + 5 * (pathWords pout).length)) 11) svc = .ok cO)
    (hf70 : cbField (after (after a (6 + 5 * (pathWords pout).length)) 13) e70 = .ok f70)
    (hld : CodeAt code (after a (21 + 5 * (pathWords pout).length)) [.ldr 1 31 1, .ldr 2 31 3])
    (hw : CodeAt code (after a (23 + 5 * (pathWords pout).length)) [.cbz 2 fd, .ldr 0 31 2,
      .movz 8 64 0, .bl cW, .cbz 0 fz, .subsReg 31 0 2, .bcond 8 fw, .addReg 1 1 0,
      .subReg 2 2 0, .b gb])
    (hfd : cbField (after a (23 + 5 * (pathWords pout).length))
      (after a (33 + 5 * (pathWords pout).length)) = .ok fd)
    (hcW : bField (after a (26 + 5 * (pathWords pout).length)) svc = .ok cW)
    (hfz : cbField (after a (27 + 5 * (pathWords pout).length)) e74 = .ok fz)
    (hfw : cbField (after a (29 + 5 * (pathWords pout).length)) e74 = .ok fw)
    (hgb : bField (after a (32 + 5 * (pathWords pout).length))
      (after a (23 + 5 * (pathWords pout).length)) = .ok gb)
    (hfin : CodeAt code (after a (33 + 5 * (pathWords pout).length))
      ([.ldr 0 31 2, .movz 8 57 0, .bl cD, .cbnz 0 f71] ++ movImm 0 0 ++
        [.ldr 30 31 0, .addImm 31 31 fr, .ret 30]))
    (hcD : bField (after a (35 + 5 * (pathWords pout).length)) svc = .ok cD)
    (hf71 : cbField (after a (36 + 5 * (pathWords pout).length)) e71 = .ok f71)
    (hs70 : CodeAt code e70 (movImm 0 (UInt64.ofNat 70) ++ [.b x70]))
    (hx70 : bField (after e70 4) base = .ok x70)
    (hs74 : CodeAt code e74 (movImm 0 (UInt64.ofNat 74) ++ [.b x74]))
    (hx74 : bField (after e74 4) base = .ok x74)
    (hs71 : CodeAt code e71 (movImm 0 (UInt64.ofNat 71) ++ [.b x71]))
    (hx71 : bField (after e71 4) base = .ok x71)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (hbase : base.toNat < 2 ^ 55)
    (hpout : pathOk pout = true)
    (hF : 32 + 8 * ((pathWords pin).length + (pathWords pout).length) ≤ stampFrame pin pout)
    (hfrv : fr.val = stampFrame pin pout)
    (houtSlot : outSlot.val = 32 + 8 * (pathWords pin).length)
    (hret0 : ret0.toNat < 2 ^ 55)
    {q : Proc} (hpc : q.core.pc = a) (hf : q.fpcr = fpcrValue)
    (hin : StampInput sp0 inMax pin pout B ec er eo rs ecl)
    (hlen : (readData eo.ret rs).length ≤ inMax.toNat)
    (htr : sysEvents q.trace = [ec, er, eo] ++ rs ++ [ecl])
    (hSPf : SPf = sp0 - UInt64.ofNat (stampFrame pin pout))
    (hsp : q.core.sp = SPf) (hal : SPf % 16 = 0) (htop : SPf.toNat < 2 ^ 63)
    (hframe : ∀ j < stampFrame pin pout, P.normal (SPf + UInt64.ofNat j) = true)
    (h18 : (q.core.x 18).toNat ≤ SPf.toNat)
    (hs0 : load64 q.core.mem (slotAddr SPf 0) = ret0)
    {st3 : Store Unit} {rootR : UInt64} {bs : List UInt8}
    (hbs : bs = Out (ec.output ++ er.output ++ readData eo.ret rs))
    (hx0 : q.core.x 0 = rootR) (hx1 : q.core.x 1 = UInt64.ofNat bs.length)
    (hsr : StoreRel P cap gts st3 q.core)
    (hfit : rootR.toNat + bs.length ≤ st3.mem.pages * 65536)
    (hbytes : ∀ i (h : i < bs.length), st3.mem.bytes (rootR.toNat + i) = bs[i]) :
    ∃ p', ProcReachWith LeanExe.Linux.table R P code q p' ∧ p'.core.io = q.core.io ∧
      ((p'.core.pc = ret0 ∧ p'.core.x 0 = 0 ∧
          StampEvents sp0 inMax pin pout Out Tr none (sysEvents p'.trace)) ∨
        (p'.core.pc = base ∧
          StampEvents sp0 inMax pin pout Out Tr (some (p'.core.x 0))
            (sysEvents p'.trace))) := by
  have hstub : ∀ (c : Nat) (a : UInt64) (g : Fin 67108864),
      CodeAt code a (movImm 0 (UInt64.ofNat c) ++ [.b g]) → (a.toNat < 2 ^ 55) :=
    fun c a g hca => by
      have := hca 0 (by simp [movImm])
      rw [after_zero] at this
      exact hdom _ _ this
  obtain ⟨hpl0, hpl64, hnz⟩ := pathOk_facts hpout
  have hwo : (pathWords pout).length = pout.length / 8 + 1 := pathWords_length pout
  have hpg := hsr.pages
  have hcapl := hsr.cap_lt
  have hbelow := hsr.below
  have hfitc : rootR.toNat + bs.length ≤ cap * 65536 :=
    Nat.le_trans hfit (Nat.mul_le_mul_right _ hpg.2)
  have hx18 := (q.core.x 18).toNat_lt
  -- the result's address into X1 and its length into X2
  have c0 := hc1 0 (by simp)
  have c1 := hc1 1 (by simp)
  have c2 := hc1 2 (by simp)
  have c3 := hc1 3 (by simp)
  have c4 := hc1 4 (by simp)
  have c5 := hc1 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5
  obtain ⟨v1, rv1, pv1, x2v1, kv1, spv1, memv1, iov1⟩ := run_setX P code (d := 2) (by decide)
    (by rw [hpc]; exact c0) (rfl : LeanExe.A64.exec P (mov 2 1) q.core = _)
  have pv1' : v1.pc = after a 1 := by rw [pv1, hpc, after_one]
  obtain ⟨v2, rv2, pv2, x1v2, kv2, spv2, memv2, iov2⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pv1']; exact c1) (rfl : LeanExe.A64.exec P (.addReg 1 17 0) v1 = _)
  have pv2' : v2.pc = after a 2 := by rw [pv2, pv1', ← after_succ]
  obtain ⟨v3, rv3, pv3, x1v3, kv3, spv3, memv3, iov3⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pv2']; exact c2)
    (exec_addImm_x P (s := v2) (d := 1) (n := 1) (imm := 2048) (by decide) (by decide))
  have pv3' : v3.pc = after a 3 := by rw [pv3, pv2', ← after_succ]
  obtain ⟨v4, rv4, pv4, x1v4, kv4, spv4, memv4, iov4⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pv3']; exact c3)
    (exec_addImm_x P (s := v3) (d := 1) (n := 1) (imm := 2048) (by decide) (by decide))
  have pv4' : v4.pc = after a 4 := by rw [pv4, pv3', ← after_succ]
  have hsp4 : v4.sp = SPf := by rw [spv4, spv3, spv2, spv1, hsp]
  have hR : v4.x 1 = q.core.x 17 + UInt64.ofNat (4096 + rootR.toNat) := by
    rw [x1v4, x1v3, x1v2, kv1 17 (by decide), kv1 0 (by decide), hx0]
    rw [show q.core.x 17 + rootR + UInt64.ofNat (2048 : Fin 4096).val +
      UInt64.ofNat (2048 : Fin 4096).val = q.core.x 17 + UInt64.ofNat rootR.toNat +
        UInt64.ofNat 2048 + UInt64.ofNat 2048 by
        rw [UInt64.ofNat_toNat]; rfl, add_ofNat_add, add_ofNat_add]
    congr 2
    omega
  have hlen2 : v4.x 2 = UInt64.ofNat bs.length := by
    rw [kv4 2 (by decide), kv3 2 (by decide), kv2 2 (by decide), x2v1]
    show q.core.x 31 ||| q.core.x 1 = _
    rw [x31_or, hx1]
  let v5 : State :=
    { v4 with mem := store64 v4.mem (slotAddr v4.sp 1) (v4.x 1), pc := v4.pc + 4 }
  have e5 : exec P (.str 1 31 1) v4 = some v5 :=
    exec_str_sp P (i := 1) (by decide) (by rw [hsp4]; exact hal)
      fun j hj => by rw [hsp4]; exact hframe _ (by omega)
  let v6 : State :=
    { v5 with mem := store64 v5.mem (slotAddr v5.sp 3) (v5.x 2), pc := v5.pc + 4 }
  have e6 : exec P (.str 2 31 3) v5 = some v6 :=
    exec_str_sp P (i := 3) (by decide) (by show v4.sp % 16 = 0; rw [hsp4]; exact hal)
      fun j hj => by show P.normal (v4.sp + _) = true; rw [hsp4]; exact hframe _ (by omega)
  have rv6 : Reach P code q.core v6 := rv1.trans (rv2.trans (rv3.trans (rv4.trans
    (reach_exec P code (by rw [pv4']; exact c4) e5
      (reach_exec P code (by show code (v4.pc + 4) = _; rw [pv4', ← after_succ]; exact c5) e6
        (.refl _))))))

  have pv6 : v6.pc = after a 6 := by
    show v4.pc + 4 + 4 = _
    rw [pv4', ← after_succ, ← after_succ]
  have hsp6 : v6.sp = SPf := hsp4
  have hmem4 : v4.mem = q.core.mem := by rw [memv4, memv3, memv2, memv1]
  have hmem6 : v6.mem = store64 (store64 q.core.mem (slotAddr SPf 1) (v4.x 1)) (slotAddr SPf 3)
      (v4.x 2) := by
    show store64 (store64 v4.mem (slotAddr v4.sp 1) (v4.x 1)) (slotAddr v4.sp 3) (v4.x 2) = _
    rw [hsp4, hmem4]
  have hk6 : ∀ r : Fin 32, r ≠ 1 → r ≠ 2 → v6.x r = q.core.x r := fun r h1 h2 => by
    show v4.x r = _
    rw [kv4 r h1, kv3 r h1, kv2 r h1, kv1 r h2]
  -- the bytes below the stack's limit keep their values
  have hlow6 : ∀ b : UInt64, b.toNat < (q.core.x 18).toNat → v6.mem b = q.core.mem b := by
    intro b hb
    rw [hmem6, store64_other _ _ _ _ (below_slot h18 htop (by decide) hb),
      store64_other _ _ _ _ (below_slot h18 htop (by decide) hb)]
  -- the stores of the output path
  have hcs' := storeWords_code hsOut hcs
  obtain ⟨t7, r7, p7, sp7, io7, k7, hin7, hout7⟩ := run_storeWords (P := P) (code := code)
    (pathWords pout) (4 + (pathWords pin).length) (s := v6) hcs' pv6 (by rw [hsp6]; exact hal)
    (by rw [hsp6]; exact htop) (fun j hj => by rw [hsp6]; exact hframe j (by omega))
  rw [hsp6] at hin7 hout7
  have p7' : t7.pc = after a (6 + 5 * (pathWords pout).length) := by rw [p7, after_after]
  have hsp7 : t7.sp = SPf := by rw [sp7, hsp6]
  have hpath : ∀ j ≤ pout.length,
      t7.mem (t7.sp + UInt64.ofNat outSlot.val + UInt64.ofNat j) = pout.getD j 0 := by
    intro j hj
    rw [hsp7, houtSlot, show SPf + UInt64.ofNat (32 + 8 * (pathWords pin).length) =
      slotAddr SPf (4 + (pathWords pin).length) by rw [slotAddr_eq]; congr 2; omega,
      hin7 j (by omega), pathWords_byte pout (by omega)]
  have hpm : ∀ j ≤ pout.length,
      P.normal (t7.sp + UInt64.ofNat outSlot.val + UInt64.ofNat j) = true := by
    intro j hj
    rw [hsp7, add_ofNat_add, houtSlot]
    exact hframe _ (by omega)
  have fq : ({ q with core := t7 } : Proc).fpcr = fpcrValue := hf
  have hreach7 : ProcReachWith LeanExe.Linux.table R P code q { q with core := t7 } :=
    ProcReachWith.of_reach' hdom hf (rv6.trans r7) (by rw [p7']; exact hdom _ _ (by
      simpa [after_zero] using hco 0 (by simp [movImm])))
  -- the open of the output
  obtain ⟨q5, eo2, rq5, fq5, ioq5, trq5, ho1, ho2, ho3, hout⟩ := run_open
    (T := LeanExe.Linux.table) (R := R) (P := P) (code := code)
    (o := after a (6 + 5 * (pathWords pout).length)) hco hcO hf70 hsvc table_openat hdom
    (by
      rw [after_after, show 6 + 5 * (pathWords pout).length + 15 =
        21 + 5 * (pathWords pout).length by omega]
      exact hdom _ _ (by simpa [after_zero] using hld 0 (by simp)))
    (hstub _ _ _ hs70) (by omega) hnz (q := { q with core := t7 }) p7' fq
    (by show t7.sp % 16 = 0; rw [hsp7]; exact hal)
    (fun j hj => by show P.normal (t7.sp + _) = true; rw [hsp7]; exact hframe j (by omega))
    hpath hpm
  have ho2' : eo2.args = [atFdcwd, sp0 - UInt64.ofNat (stampFrame pin pout) +
      UInt64.ofNat (32 + 8 * (pathWords pin).length), stampOutFlags, 420] := by
    rw [ho2, show ({ q with core := t7 } : Proc).core.sp = SPf from hsp7, houtSlot, hSPf]
    rfl
  have htr5 : sysEvents q5.trace = [ec, er, eo] ++ rs ++ [ecl, eo2] := by
    rw [trq5, sysEvents_snoc]
    show sysEvents q.trace ++ _ = _
    rw [htr]
    simp
  have hio5 : q5.core.io = q.core.io := by
    rw [ioq5]
    show t7.io = _
    rw [io7]
    show v4.io = _
    rw [iov4, iov3, iov2, iov1]
  rcases hout with ⟨hge, pq5⟩ | ⟨hlt, pq5, spq5, memq5, kq5⟩
  · obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs70 hx70 hdom hbase pq5 fq5
    refine ⟨q', hreach7.trans (rq5.trans rq'), by rw [ioq', hio5], .inr ⟨pq', ?_⟩⟩
    rw [xq', trq', htr5]
    exact StampEvents.openOut hin hlen ho1 ho2' ho3 hge
  -- the memory after the open: the slots and the area
  have hmem5 : q5.core.mem = store64 t7.mem (slotAddr SPf 2) eo2.ret := by
    rw [memq5]
    show store64 t7.mem (slotAddr t7.sp 2) eo2.ret = _
    rw [hsp7]
  have hslot5 : ∀ i, i < 4 → i ≠ 2 → ∀ k < 8,
      q5.core.mem (slotAddr SPf i + UInt64.ofNat k) = v6.mem (slotAddr SPf i + UInt64.ofNat k) :=
    fun i hi h2 k hk => by
      rw [hmem5, store64_other _ _ _ _
        (slot_apart (sp := SPf) (i := 2) (j := i) (by decide) (by omega) (by omega) k hk),
        hout7 _ (below_slots (by omega) (by omega) k hk)]
  have hR' : load64 q5.core.mem (slotAddr SPf 1) = v4.x 1 := by
    rw [load64_congr (m' := v6.mem) (hslot5 1 (by decide) (by decide)), hmem6,
      load64_store64_other _ _ _ _
        (slot_apart (sp := SPf) (i := 3) (j := 1) (by decide) (by decide) (by decide)),
      load64_store64_same]
  have hL' : load64 q5.core.mem (slotAddr SPf 3) = v4.x 2 := by
    rw [load64_congr (m' := v6.mem) (hslot5 3 (by decide) (by decide)), hmem6,
      load64_store64_same]
  have h0' : load64 q5.core.mem (slotAddr SPf 0) = ret0 := by
    rw [load64_congr (m' := v6.mem) (hslot5 0 (by decide) (by decide)), hmem6,
      load64_store64_other _ _ _ _
        (slot_apart (sp := SPf) (i := 3) (j := 0) (by decide) (by decide) (by decide)),
      load64_store64_other _ _ _ _
        (slot_apart (sp := SPf) (i := 1) (j := 0) (by decide) (by decide) (by decide)), hs0]
  have hlow5 : ∀ b : UInt64, b.toNat < (q.core.x 18).toNat → q5.core.mem b = q.core.mem b := by
    intro b hb
    have hXe := toNat_slot SPf (4 + (pathWords pin).length)
    have hbt := b.toNat_lt
    rw [hmem5, store64_other _ _ _ _ (below_slot h18 htop (by decide) hb), hout7 b ?_, hlow6 b hb]
    rw [UInt64.toNat_sub, hXe]
    simp only [Nat.reducePow] at *
    omega
  have hk5 : ∀ r : Fin 32, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 8 → r ≠ 16 → r ≠ 30 →
      q5.core.x r = q.core.x r := fun r h0 h1 h2 h3 h8 h16 h30 => by
    rw [kq5 r h0 h1 h2 h3 h8 h16 h30]
    show t7.x r = _
    rw [k7 r h16, hk6 r h1 h2]
  -- the result's address and length into X1 and X2
  have cl0 := hld 0 (by simp)
  have cl1 := hld 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, after_zero] at cl0 cl1
  have pq5' : q5.core.pc = after a (21 + 5 * (pathWords pout).length) := by
    rw [pq5, after_after]
    congr 1
    omega
  have hsp5 : q5.core.sp = SPf := by rw [spq5]; exact hsp7
  obtain ⟨y1, ry1, py1, x1y1, ky1, spy1, memy1, ioy1⟩ := run_setX P code (d := 1) (by decide)
    (by rw [pq5']; exact cl0) (exec_ldr_sp P (s := q5.core) (r := 1) (i := 1) _
      (by rw [hsp5]; exact hal) fun j hj => by rw [hsp5]; exact hframe _ (by omega))
  obtain ⟨y2, ry2, py2, x2y2, ky2, spy2, memy2, ioy2⟩ := run_setX P code (d := 2) (by decide)
    (by rw [py1, pq5', ← after_succ]; exact cl1) (exec_ldr_sp P (s := y1) (r := 2) (i := 3) _
      (by rw [spy1, hsp5]; exact hal) fun j hj => by rw [spy1, hsp5]; exact hframe _ (by omega))
  have py2' : y2.pc = after a (23 + 5 * (pathWords pout).length) := by
    rw [py2, py1, pq5', ← after_succ, ← after_succ]
    congr 1
    omega
  have hy1 : y2.x 1 = q.core.x 17 + UInt64.ofNat (4096 + rootR.toNat) := by
    rw [ky2 1 (by decide), x1y1, hsp5, hR', hR]
  have hy2 : y2.x 2 = UInt64.ofNat bs.length := by
    rw [x2y2, spy1, hsp5, memy1, hL', hlen2]
  have hmemy2 : y2.mem = q5.core.mem := by rw [memy2, memy1]
  have hspy2 : y2.sp = SPf := by rw [spy2, spy1, hsp5]
  have hreach5 : ProcReachWith LeanExe.Linux.table R P code q { q5 with core := y2 } :=
    hreach7.trans (rq5.trans (ProcReachWith.of_reach' hdom fq5 (ry1.trans ry2) (by
      rw [py2']; exact hdom _ _ (by simpa [after_zero] using hw 0 (by simp)))))
  -- the store at the write loop and the result's bytes
  have hx17y : y2.x 17 = q.core.x 17 := by
    rw [ky2 17 (by decide), ky1 17 (by decide), hk5 17 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  have hx18y : y2.x 18 = q.core.x 18 := by
    rw [ky2 18 (by decide), ky1 18 (by decide), hk5 18 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  have hsry : StoreRel P cap gts st3 y2 := hsr.congr hx17y hx18y fun b hb => by
    rw [hmemy2]
    exact hlow5 b hb
  have hbsl : readList y2.mem (y2.x 1) bs.length = bs := by
    rw [hy1, ← hx17y, readList_bytes P hsry bs.length rootR.toNat hfitc,
      memBytes_eq st3.mem bs rootR.toNat hbytes]
  -- the write loop
  have hW := fun n => after_after a (23 + 5 * (pathWords pout).length) n
  obtain ⟨p6, ws, rp6, fp6, iop6, trp6, res6⟩ := run_stampWriteLoop (T := LeanExe.Linux.table)
    (R := R) (P := P) (code := code) (W := after a (23 + 5 * (pathWords pout).length)) hw
    (by rw [hW, show 23 + 5 * (pathWords pout).length + 10 = 33 + 5 * (pathWords pout).length by
      omega]; exact hfd)
    (by rw [hW, show 23 + 5 * (pathWords pout).length + 3 = 26 + 5 * (pathWords pout).length by
      omega]; exact hcW)
    (by rw [hW, show 23 + 5 * (pathWords pout).length + 4 = 27 + 5 * (pathWords pout).length by
      omega]; exact hfz)
    (by rw [hW, show 23 + 5 * (pathWords pout).length + 6 = 29 + 5 * (pathWords pout).length by
      omega]; exact hfw)
    (by rw [hW, show 23 + 5 * (pathWords pout).length + 9 = 32 + 5 * (pathWords pout).length by
      omega]; exact hgb)
    hsvc table_write hdom
    (by rw [hW, show 23 + 5 * (pathWords pout).length + 10 = 33 + 5 * (pathWords pout).length by
      omega]; exact hdom _ _ (by simpa [after_zero] using hfin 0 (by simp)))
    (hstub _ _ _ hs74) eo2.ret SPf hal (fun j hj => hframe j (by omega)) bs.length
    { q5 with core := y2 } py2' fq5 hy2 (by omega)
    (fun i hi => by
      show P.normal (y2.x 1 + _) = true
      rw [hy1, add_ofNat_add, ← hx17y]
      exact hsry.mapped _ (by unfold areaSize; omega))
    hspy2 (by show load64 y2.mem _ = _; rw [hmemy2, hmem5, load64_store64_same])
  have htr6 : ∀ tr, sysEvents tr = sysEvents ({ q5 with core := y2 } : Proc).trace ++ ws →
      sysEvents tr = [ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws := fun tr h => by
    rw [h]
    show sysEvents q5.trace ++ ws = _
    rw [htr5]
  have hio6 : p6.core.io = q.core.io := by
    rw [iop6]
    show y2.io = _
    rw [ioy2, ioy1, hio5]
  rcases res6 with ⟨pc6, hwl, j, hj, hwd⟩ | ⟨pc6, hwl, hwd, memp6, spp6, kp6⟩
  · -- a write failed: the stub of status 74
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs74 hx74 hdom hbase pc6 fp6
    refine ⟨q', hreach5.trans (rp6.trans rq'), by rw [ioq', hio6], .inr ⟨pq', ?_⟩⟩
    rw [xq', trq', htr6 _ trp6]
    refine StampEvents.write74 hin hlen ho1 ho2' ho3 hlt (by rw [← hbs]; exact hwl) ?_
    rw [hwd, ← hbs, ← hbsl]
    refine ⟨readList y2.mem (y2.x 1 + UInt64.ofNat j) (bs.length - j), ?_⟩
    show readList y2.mem (y2.x 1) j ++ _ = _
    rw [← readList_add, Nat.add_sub_cancel' hj]
  -- every byte written: the output's close and the return
  have hsf := CodeAt.split code hfin (l1 := [.ldr 0 31 2, .movz 8 57 0, .bl cD, .cbnz 0 f71] ++
    movImm 0 0) (n := 8) (by simp [movImm])
  have hsc := CodeAt.split code hsf.1 (l1 := [.ldr 0 31 2, .movz 8 57 0, .bl cD, .cbnz 0 f71])
    (n := 4) rfl
  simp only [after_after] at hsc hsf
  have pc6' : p6.core.pc = after a (33 + 5 * (pathWords pout).length) := by
    rw [pc6, after_after]
    congr 1
    omega
  have hsp6' : p6.core.sp = SPf := by rw [spp6]; exact hspy2
  have hmem6' : p6.core.mem = q5.core.mem := by rw [memp6]; exact hmemy2
  have hx18p6 : p6.core.x 18 = q.core.x 18 := by
    rw [kp6 18 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx18y
  obtain ⟨p7, ecl2, rp7, fp7, iop7, trp7, hc1', hc2', res7⟩ := run_close (T := LeanExe.Linux.table)
    (R := R) (P := P) (code := code) hsc.1
    (by rw [after_after, show 33 + 5 * (pathWords pout).length + 2 =
      35 + 5 * (pathWords pout).length by omega]; exact hcD)
    (by rw [after_after, show 33 + 5 * (pathWords pout).length + 3 =
      36 + 5 * (pathWords pout).length by omega]; exact hf71)
    hsvc table_close hdom
    (by rw [after_after]; exact hdom _ _ (by
      have := hsc.2 0 (by simp [movImm])
      rw [after_zero] at this
      exact this))
    (hstub _ _ _ hs71) pc6' fp6 (by rw [hsp6']; exact hal)
    (fun j hj => by rw [hsp6']; exact hframe j (by omega))
  rw [hsp6', hmem6', hmem5, load64_store64_same] at hc2'
  have htr7 : sysEvents p7.trace = [ec, er, eo] ++ rs ++ [ecl, eo2] ++ ws ++ [ecl2] := by
    rw [trp7, sysEvents_snoc, htr6 _ trp6]
  have hout7' : writeData eo2.ret ws = Out (ec.output ++ er.output ++ readData eo.ret rs) := by
    rw [hwd, ← hbs, hbsl]
  have hwl' : WriteLoop eo2.ret false (y2.x 1)
      (Out (ec.output ++ er.output ++ readData eo.ret rs)).length ws := by
    rw [← hbs]; exact hwl
  rcases res7 with ⟨hne, pc7⟩ | ⟨h0, pc7, sp7', mem7, k7'⟩
  · -- the close failed: the stub of status 71
    obtain ⟨q', rq', pq', xq', trq', ioq'⟩ := run_stubWith (T := LeanExe.Linux.table) (R := R)
      hs71 hx71 hdom hbase pc7 fp7
    refine ⟨q', hreach5.trans (rp6.trans (rp7.trans rq')), by rw [ioq', iop7, hio6],
      .inr ⟨pq', ?_⟩⟩
    rw [xq', trq', htr7]
    exact StampEvents.close71 hin hlen ho1 ho2' ho3 hlt hwl' hout7' hc1' hc2'
      (.inl ⟨rfl, hne⟩)
  -- the return
  have pc7' : p7.core.pc = after a (33 + 5 * (pathWords pout).length + 4) := by
    rw [pc7, after_after]
  obtain ⟨z1, rz1, pz1, x0z1, kz1, spz1, memz1, ioz1⟩ := run_movImm P code (d := 0) (v := 0)
    (by decide) hsc.2 pc7'
  have hsp7 : p7.core.sp = SPf := by rw [sp7']; exact hsp6'
  obtain ⟨z2, rz2, pz2, spz2, ioz2, memz2, kz2⟩ := run_epilogue P code (n := 0) (fs := fr.val)
    fr.isLt (by decide) (s := z1) (a := after a (33 + 5 * (pathWords pout).length + 8)) hsf.2
    (by rw [pz1, after_after]) (by rw [spz1, hsp7]; exact hal)
    (fun j hj => by rw [spz1, hsp7]; exact hframe _ (by omega))
  have hpcz : z2.pc = ret0 := by
    rw [pz2, spz1, hsp7, memz1, mem7, hmem6', h0']
  refine ⟨{ p7 with core := z2 }, hreach5.trans (rp6.trans (rp7.trans
    (ProcReachWith.of_reach' hdom fp7 (rz1.trans rz2) (by rw [hpcz]; exact hret0)))), ?_,
    .inl ⟨hpcz, ?_, ?_⟩⟩
  · show z2.io = _
    rw [ioz2, ioz1, iop7, hio6]
  · rw [kz2 0 (by decide), x0z1]
  · show StampEvents _ _ _ _ _ _ _ (sysEvents p7.trace)
    rw [htr7]
    exact StampEvents.close71 hin hlen ho1 ho2' ho3 hlt hwl' hout7' hc1' hc2'
      (.inr ⟨rfl, h0⟩)

end LeanExe.A64
