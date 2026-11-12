import LeanExe.A64.Proof.Linux
import LeanExe.A64.Proof.BytesMain
import LeanExe.A64.Elf

/-!
The loops of `genSysMain`, the entry routine of a Linux executable.  `run_readLoop` follows the
loop that reads standard input into the block from the allocator: by strong induction on the bytes
of the block that remain, each pass calls `sysRead`, adds the bytes that the read returned to the
block, and steps the address and the count, until a read returns 0, which leaves the loop with all
of the input in the block, or the block is full, which branches to the stub of status 64.
`run_writeLoop` follows the loop that writes the result's bytes to standard output, by strong
induction on the bytes that remain, each pass a call of `sysWrite` that takes some of them.  Both
assume that no call fails.  `StoreRel.writeList` gives the store relation after the kernel writes
bytes into linear memory, and `readList_bytes` the bytes that a write takes from it.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- `SUBS XZR, Xx, Xy` and `B.HI` at `a`: the run reaches `tB` when `Xx` lies above `Xy` and the
next instruction otherwise, changing the flags alone. -/
theorem run_hiReg {a tB : UInt64} {g : Fin 524288} {x y : Fin 32}
    (hcode : CodeAt code a [.subsReg 31 x y, .bcond 8 g]) (hg : cbField (after a 1) tB = .ok g)
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if s.x y < s.x x then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x x) (s.x y) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsReg 31 x y) s = some s1 := rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 8 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 8 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_succ, after_zero]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x x - s.x y)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 8 = decide (s.x y < s.x x) := by
    rw [condHolds_8]
    show (decide (s.x y ≤ s.x x) && !(s.x x - s.x y == 0)) = _
    exact cond_hi _ _
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 8 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : s.x y < s.x x
    · rw [ite_eq_left (by simpa using h), ite_eq_left h]
      exact cbField_target hg
    · rw [ite_eq_right (by simpa using h), ite_eq_right h, ← after_succ]
  · show (s.setX 31 (s.x x - s.x y)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x x - s.x y)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x x - s.x y)).io = _
    exact State.setX_io

/-! ## Bytes that the kernel writes and reads -/

/-- The store with the bytes `as ++ bs` written from `p` is the store with `as` written from `p`
and then `bs` after them. -/
theorem storeBytes_append :
    ∀ (st : Store Unit) (p : Nat) (as bs : List UInt8),
      storeBytes st p (as ++ bs) = storeBytes (storeBytes st p as) (p + as.length) bs
  | _, _, [], _ => rfl
  | st, p, a :: as, bs => by
    rw [List.cons_append, storeBytes, storeBytes, storeBytes_append _ (p + 1) as bs,
      List.length_cons, show p + 1 + as.length = p + (as.length + 1) by omega]

/-- The store relation after the kernel writes the bytes `bs` from byte `p` of linear memory,
within the memory's size. -/
theorem StoreRel.kernelWrite {cap : Nat} {gts : List ValueType} :
    ∀ (bs : List UInt8) (st : Store Unit) (s : State) (p : Nat), StoreRel P cap gts st s →
      p + bs.length ≤ st.mem.pages * 65536 →
      StoreRel P cap gts (storeBytes st p bs)
        { s with mem := writeList s.mem (s.x 17 + UInt64.ofNat (4096 + p)) bs }
  | [], st, s, p, h, _ => h
  | b :: bs, st, s, p, h, hp => by
    have hcap := h.cap_lt
    have hpg := h.pages
    have hpp : st.mem.pages * 65536 ≤ 65536 * 65536 := Nat.mul_le_mul_right _ (by omega)
    simp only [List.length_cons] at hp
    have hp32 : (UInt32.ofNat p).toNat = p := by
      rw [UInt32.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have h1 : StoreRel P cap gts { st with mem := st.mem.write8 (UInt32.ofNat p) b }
        { s with mem := store8 s.mem (s.x 17 + UInt64.ofNat (4096 + p)) b } :=
      h.write8 P (y := UInt32.ofNat p) (by rw [hp32]; omega) rfl rfl (by rw [hp32])
    have h2 := StoreRel.kernelWrite bs _ _ (p + 1) h1 (by
      show p + 1 + bs.length ≤ (st.mem.write8 _ _).pages * 65536
      simp only [Mem.write8]
      omega)
    have e : s.x 17 + UInt64.ofNat (4096 + p) + 1 = s.x 17 + UInt64.ofNat (4096 + (p + 1)) := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, add_ofNat_add, Nat.add_assoc]
    simp only [storeBytes, LeanExe.A64.writeList]
    rw [e]
    exact h2

/-- The bytes of `readList` of `r + n` bytes are those of the first `r` and then those of the
next `n`. -/
theorem readList_add (m : UInt64 → UInt8) :
    ∀ (a : UInt64) (r n : Nat), readList m a (r + n) = readList m a r ++
      readList m (a + UInt64.ofNat r) n
  | a, 0, n => by simp [readList, add_ofNat_zero]
  | a, r + 1, n => by
    rw [show r + 1 + n = (r + n) + 1 by omega, readList, readList, readList_add m (a + 1) r n,
      List.cons_append, show a + 1 + UInt64.ofNat r = a + UInt64.ofNat (r + 1) by
        rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, add_ofNat_add, Nat.add_comm]]

/-- The bytes that `readList` takes from linear memory, where the machine holds the store `st`,
are those of `st`'s memory. -/
theorem readList_bytes {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α}
    {s : State} (h : StoreRel P cap gts st s) :
    ∀ (n p : Nat), p + n ≤ cap * 65536 →
      readList s.mem (s.x 17 + UInt64.ofNat (4096 + p)) n = memBytes st.mem p n
  | 0, _, _ => rfl
  | n + 1, p, hp => by
    rw [readList, memBytes, h.bytes p (by omega), show s.x 17 + UInt64.ofNat (4096 + p) + 1 =
        s.x 17 + UInt64.ofNat (4096 + (p + 1)) by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, add_ofNat_add, Nat.add_assoc],
      readList_bytes h n (p + 1) (by omega)]

/-! ## The read loop -/

theorem ofNat_ne_zero {r : Nat} (h0 : 0 < r) (h : r < 2 ^ 64) : UInt64.ofNat r ≠ 0 := by
  intro e
  have := congrArg UInt64.toNat e
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h] at this
  simp at this
  omega

theorem ofNat_sub_ofNat {c r : Nat} (hr : r ≤ c) (hc : c < 2 ^ 64) :
    UInt64.ofNat c - UInt64.ofNat r = UInt64.ofNat (c - r) := by
  have e1 : (UInt64.ofNat c).toNat = c := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hc
  have e2 : (UInt64.ofNat r).toNat = r := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have e3 : (UInt64.ofNat (c - r)).toNat = c - r := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  apply UInt64.toNat_inj.mp
  rw [toNat_sub_le (by rw [e1, e2]; exact hr), e1, e2, e3]

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]

/-- The part of a pass of the read loop after the call, from the `CBZ` at `after H 2`, with the
read's count `r` in X0 and the block's remaining bytes `c`, at least `r`, in X2: a count of 0
reaches the end of input at `after H 9`, a count below `c` steps X1 and X2 and returns to the
loop's head `H`, and a count of `c` reaches the stub of status 64 at `e64`. -/
theorem run_readTail {H e64 e65 : UInt64} {fe fl fr : Fin 524288} {go : Fin 67108864}
    (hc : CodeAt code (after H 2) [.cbz 0 fe, .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0,
      .subReg 2 2 0, .cbnz 2 fr, .b go])
    (hfe : cbField (after H 2) (after H 9) = .ok fe) (hfl : cbField (after H 4) e65 = .ok fl)
    (hfr : cbField (after H 7) H = .ok fr) (hgo : bField (after H 8) e64 = .ok go)
    {s : State} (hpc : s.pc = after H 2) {r c : Nat} (hr : r ≤ c) (hc64 : c < 2 ^ 64)
    (h0 : s.x 0 = UInt64.ofNat r) (h2 : s.x 2 = UInt64.ofNat c) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 1 → q ≠ 2 → t.x q = s.x q) ∧
      ((r = 0 ∧ t.pc = after H 9 ∧ t.x 1 = s.x 1 ∧ t.x 2 = s.x 2) ∨
        (0 < r ∧ r < c ∧ t.pc = H ∧ t.x 1 = s.x 1 + UInt64.ofNat r ∧
          t.x 2 = UInt64.ofNat (c - r)) ∨
        (0 < r ∧ r = c ∧ t.pc = e64)) := by
  have c0 := hc 0 (by simp)
  have c5 := hc 5 (by simp)
  have c6 := hc 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c0 c5 c6
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · refine ⟨{ s with pc := after H 9 }, cbz_taken P code (by rw [hpc]; exact c0) hpc hfe
      (by rw [h0]; rfl), rfl, rfl, rfl, fun _ _ _ => rfl, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
  have hr64 : r < 2 ^ 64 := by omega
  let s1 : State := { s with pc := s.pc + 4 }
  have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0)
    (cbz_next P (by rw [h0]; exact ofNat_ne_zero hpos hr64)) (.refl _)
  have p1 : s1.pc = after H 3 := by show s.pc + 4 = _; rw [hpc, ← after_succ]
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c1 c2
  have hhi' : CodeAt code (after H 3) [.subsReg 31 0 2, .bcond 8 fl] :=
    CodeAt.cons.mpr ⟨c1, CodeAt.cons.mpr ⟨by rw [after_after]; exact c2,
      fun i hi => absurd hi (by simp)⟩⟩
  obtain ⟨s2, r2, p2, x2, sp2, mem2, io2⟩ := run_hiReg P code (x := 0) (y := 2) hhi'
    (by rw [after_after]; exact hfl) p1
  have hnlt : ¬ s1.x 2 < s1.x 0 := by
    show ¬ s.x 2 < s.x 0
    rw [h0, h2, ofNat_lt_ofNat hc64 hr64]
    omega
  rw [if_neg hnlt, after_after] at p2
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c3 c4
  obtain ⟨s3, r3, p3, x13, k3, sp3, mem3, io3⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p2]; exact c3) (rfl : LeanExe.A64.exec P (.addReg 1 1 0) s2 = _)
  obtain ⟨s4, r4, p4, x24, k4, sp4, mem4, io4⟩ := run_setX P code (d := 2) (by decide)
    (by rw [p3, p2, ← after_succ]; exact c4) (rfl : LeanExe.A64.exec P (.subReg 2 2 0) s3 = _)
  have p4' : s4.pc = after H 7 := by rw [p4, p3, p2, ← after_succ, ← after_succ]
  have hx1 : s4.x 1 = s.x 1 + UInt64.ofNat r := by
    rw [k4 1 (by decide), x13, x2 1, x2 0]
    show s.x 1 + s.x 0 = _
    rw [h0]
  have hx2 : s4.x 2 = UInt64.ofNat (c - r) := by
    rw [x24, k3 2 (by decide), k3 0 (by decide), x2 2, x2 0]
    show s.x 2 - s.x 0 = _
    rw [h0, h2, ofNat_sub_ofNat hr hc64]
  have hk4 : ∀ q : Fin 32, q ≠ 1 → q ≠ 2 → s4.x q = s.x q := fun q h1 h2' => by
    rw [k4 q h2', k3 q h1, x2 q]
    rfl
  have hsp4 : s4.sp = s.sp := by rw [sp4, sp3, sp2]
  have hmem4 : s4.mem = s.mem := by rw [mem4, mem3, mem2]
  have hio4 : s4.io = s.io := by rw [io4, io3, io2]
  let s5 : State := { s4 with pc := if s4.x 2 ≠ 0 then s4.pc + sext 19 fr.val * 4 else s4.pc + 4 }
  have r5 : Reach P code s4 s5 := reach_exec P code (by rw [p4']; exact c5) rfl (.refl _)
  have r15 : Reach P code s s5 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  rcases Nat.lt_or_ge r c with hlt | hge
  · have hne : s4.x 2 ≠ 0 := by rw [hx2]; exact ofNat_ne_zero (by omega) (by omega)
    refine ⟨s5, r15, hsp4, hmem4, hio4, hk4, .inr (.inl ⟨hpos, hlt, ?_, hx1, hx2⟩)⟩
    show (if s4.x 2 ≠ 0 then s4.pc + sext 19 fr.val * 4 else s4.pc + 4) = H
    rw [if_pos hne, p4']
    exact cbField_target hfr
  · have hrc : r = c := by omega
    have heq : s4.x 2 = 0 := by rw [hx2, show c - r = 0 by omega]; rfl
    have p5 : s5.pc = after H 8 := by
      show (if s4.x 2 ≠ 0 then s4.pc + sext 19 fr.val * 4 else s4.pc + 4) = _
      rw [if_neg (by simp [heq]), p4', ← after_succ]
    let s6 : State := { s5 with pc := s5.pc + sext 26 go.val * 4 }
    have r6 : Reach P code s5 s6 := reach_exec P code (by rw [p5]; exact c6) rfl (.refl _)
    exact ⟨s6, r15.trans r6, hsp4, hmem4, hio4, hk4, .inr (.inr ⟨hpos, hrc, by
      show s5.pc + sext 26 go.val * 4 = e64
      rw [p5]
      exact bField_target hgo⟩)⟩

theorem after_one (a : UInt64) : after a 1 = a + 4 := by simp [after]

theorem add_four_four (a : UInt64) : a + 4 + 4 = a + 8 := by
  rw [UInt64.add_assoc]
  rfl

/-- One pass of the read loop from its head `H`, with `c` bytes of the block left in X2, when the
call does not fail and the bytes that it returns lie in Normal memory: `MOVZ X0, #0`, the call of
`sysRead` at `rd`, which returns `r` bytes, at most `c`, and writes them from X1, and the rest of
the pass that `run_readTail` follows. -/
theorem run_readPass {K : Kernel} {H e64 e65 rd : UInt64} {fe fl fr : Fin 524288}
    {gr go : Fin 67108864}
    (hc : CodeAt code H [.movz 0 0 0, .bl gr, .cbz 0 fe, .subsReg 31 0 2, .bcond 8 fl,
      .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b go])
    (hgr : bField (after H 1) rd = .ok gr) (hfe : cbField (after H 2) (after H 9) = .ok fe)
    (hfl : cbField (after H 4) e65 = .ok fl) (hfr : cbField (after H 7) H = .ok fr)
    (hgo : bField (after H 8) e64 = .ok go)
    (hrd : OpsAt code rd [.ins (.movz 8 63 0), .svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (h9 : (after H 9).toNat < 2 ^ 55) (h64 : e64.toNat < 2 ^ 55)
    {p : Proc} (hpc : p.core.pc = H) (hf : p.fpcr = fpcrValue)
    (hok : K.fail p.trace.length = none) {c : Nat} (hc64 : c < 2 ^ 64)
    (h2 : p.core.x 2 = UInt64.ofNat c) {r : Nat}
    (hr : min (K.size p.trace.length + 1) (min c (K.rest p.trace).length) = r)
    (hmap : P.mapped (p.core.x 1) c = true) :
    ∃ p', ProcReach K P code p p' ∧ p'.fpcr = fpcrValue ∧
      p'.trace = p.trace ++ [.read ((K.rest p.trace).take r)] ∧
      p'.core.mem = writeList p.core.mem (p.core.x 1) ((K.rest p.trace).take r) ∧
      p'.core.sp = p.core.sp ∧ p'.core.io = p.core.io ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 8 → q ≠ 30 → p'.core.x q = p.core.x q) ∧
      ((r = 0 ∧ p'.core.pc = after H 9 ∧ p'.core.x 1 = p.core.x 1 ∧ p'.core.x 2 = p.core.x 2) ∨
        (0 < r ∧ r < c ∧ p'.core.pc = H ∧ p'.core.x 1 = p.core.x 1 + UInt64.ofNat r ∧
          p'.core.x 2 = UInt64.ofNat (c - r)) ∨
        (0 < r ∧ r = c ∧ p'.core.pc = e64)) := by
  have hrc : r ≤ c := by rw [← hr]; omega
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  -- MOVZ X0, #0 and BL sysRead
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ :=
    run_movz P code (d := 0) (v := 0) (by decide) (by rw [hpc]; exact c0)
  have p1' : t1.pc = after H 1 := by rw [p1, hpc, after_one]
  let t2 : State := { t1.setX 30 (t1.pc + 4) with pc := t1.pc + sext 26 gr.val * 4 }
  have r2 : Reach P code p.core t2 :=
    r1.trans (reach_exec P code (by rw [p1']; exact c1) rfl (.refl _))
  have p2 : t2.pc = rd := by
    show t1.pc + sext 26 gr.val * 4 = rd
    rw [p1']
    exact bField_target hgr
  have h302 : t2.x 30 = after H 2 := by
    rw [State.x_withPc, State.x_setX_same (by decide), p1', ← after_succ]
  have hk2 : ∀ q : Fin 32, q ≠ 0 → q ≠ 30 → t2.x q = p.core.x q := fun q h0 h30 => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h30), k1 q h0]
  have hrd0 := hrd 0 (by simp)
  simp only [after_zero, List.getElem_cons_zero] at hrd0
  have q2 : ProcReach K P code p { p with core := t2 } :=
    ProcReach.of_reach' hdom hf r2 (by rw [p2]; exact hdom _ _ hrd0)
  -- the call
  let pp : Proc := { p with core := t2 }
  have hx2 : ((pp.enter (UInt64.ofNat (63 : Fin 65536).val)).core.x 2).toNat = c := by
    rw [Proc.enter_x _ _ (by decide)]
    show (t2.x 2).toNat = c
    rw [hk2 2 (by decide) (by decide), h2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc64]
  have hx1 : (pp.enter (UInt64.ofNat (63 : Fin 65536).val)).core.x 1 = p.core.x 1 := by
    rw [Proc.enter_x _ _ (by decide)]
    exact hk2 1 (by decide) (by decide)
  have hsvc := svc_read (K := K) (P := P) (p := pp.enter (UInt64.ofNat (63 : Fin 65536).val))
    (by rw [Proc.enter_x8]; rfl)
    (by
      rw [Proc.enter_x _ _ (by decide)]
      show (t1.setX 30 (t1.pc + 4)).x 0 = 0
      rw [State.x_setX_ne (by decide), x01]
      rfl)
    hok (by rw [hx2, hx1]; exact hmap)
  have htr2 : pp.trace = p.trace := rfl
  rw [hx2, hx1, Proc.enter_trace, htr2, hr] at hsvc
  have q3 := run_svcCall (K := K) (P := P) (code := code) (p := pp) hrd hdom p2 hsvc
    (by rw [Proc.ret_pc, Proc.enter_pc]; exact add_four_four _)
    (by rw [Proc.ret_x _ _ _ _ (by decide), Proc.enter_x _ _ (by decide)])
    (by show (t2.x 30).toNat < 2 ^ 55; rw [h302]; exact hdom _ _ c2)
  -- the rest of the pass
  generalize hp3 : ((pp.enter (UInt64.ofNat (63 : Fin 65536).val)).ret (UInt64.ofNat r)
    (writeList (pp.enter (UInt64.ofNat (63 : Fin 65536).val)).core.mem (p.core.x 1)
      ((K.rest pp.trace).take r)) (.read ((K.rest pp.trace).take r))).goto (pp.core.x 30) = p3
    at q3
  have p3pc : p3.core.pc = after H 2 := by rw [← hp3, Proc.goto_pc]; exact h302
  have p3x0 : p3.core.x 0 = UInt64.ofNat r := by rw [← hp3, Proc.goto_x, Proc.ret_x0]
  have p3x : ∀ q : Fin 32, q ≠ 0 → q ≠ 8 → p3.core.x q = t2.x q := fun q h0 h8 => by
    rw [← hp3, Proc.goto_x, Proc.ret_x _ _ _ _ h0, Proc.enter_x _ _ h8]
  have p3x2 : p3.core.x 2 = UInt64.ofNat c := by
    rw [p3x 2 (by decide) (by decide), hk2 2 (by decide) (by decide), h2]
  have p3mem : p3.core.mem = writeList p.core.mem (p.core.x 1) ((K.rest p.trace).take r) := by
    rw [← hp3, Proc.goto_mem, Proc.ret_mem, Proc.enter_mem]
    show writeList (t1.setX 30 (t1.pc + 4)).mem _ _ = _
    rw [State.setX_mem, mem1]
  have p3sp : p3.core.sp = p.core.sp := by
    rw [← hp3, Proc.goto_sp, Proc.ret_sp, Proc.enter_sp]
    show (t1.setX 30 (t1.pc + 4)).sp = _
    rw [State.setX_sp, sp1]
  have p3io : p3.core.io = p.core.io := by
    rw [← hp3, Proc.goto_io, Proc.ret_io, Proc.enter_io]
    show (t1.setX 30 (t1.pc + 4)).io = _
    rw [State.setX_io, io1]
  have p3tr : p3.trace = p.trace ++ [.read ((K.rest p.trace).take r)] := by
    rw [← hp3, Proc.goto_trace, Proc.ret_trace, Proc.enter_trace]
  have p3f : p3.fpcr = fpcrValue := by
    rw [← hp3, Proc.goto_fpcr, Proc.ret_fpcr, Proc.enter_fpcr]
    exact hf
  have hct : CodeAt code (after H 2) [.cbz 0 fe, .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0,
      .subReg 2 2 0, .cbnz 2 fr, .b go] := by
    have := (CodeAt.split code (l1 := [.movz 0 0 0, .bl gr]) hc rfl).2
    exact this
  obtain ⟨t, rt, spt, memt, iot, kt, out⟩ := run_readTail P code hct hfe hfl hfr hgo p3pc hrc
    hc64 p3x0 p3x2
  have hend : t.pc.toNat < 2 ^ 55 := by
    rcases out with ⟨-, e, -, -⟩ | ⟨-, -, e, -, -⟩ | ⟨-, -, e⟩ <;> rw [e]
    · exact h9
    · exact hdom _ _ (by simpa [after_zero] using hc 0 (by simp))
    · exact h64
  have q4 := ProcReach.of_reach' (K := K) hdom p3f rt hend
  refine ⟨{ p3 with core := t }, q2.trans (q3.trans q4), p3f, p3tr, by rw [memt, p3mem],
    by rw [spt, p3sp], by rw [iot, p3io], fun q h0 h1 h2' h8 h30 => ?_, ?_⟩
  · show t.x q = _
    rw [kt q h1 h2', p3x q h0 h8, hk2 q h0 h30]
  · have hx1' : p3.core.x 1 = p.core.x 1 := by
      rw [p3x 1 (by decide) (by decide), hk2 1 (by decide) (by decide)]
    rcases out with ⟨h0r, e, e1, e2⟩ | ⟨h0r, hlt, e, e1, e2⟩ | ⟨h0r, hrc', e⟩
    · exact .inl ⟨h0r, e, by show t.x 1 = _; rw [e1, hx1'], by
        show t.x 2 = _; rw [e2, p3x2, h2]⟩
    · exact .inr (.inl ⟨h0r, hlt, e, by show t.x 1 = _; rw [e1, hx1'], e2⟩)
    · exact .inr (.inr ⟨h0r, hrc', e⟩)

/-- Every one of `k` bytes from `a` that a test gives as Normal memory makes the range mapped. -/
theorem mapped_of_all {a : UInt64} {k : Nat} (h : ∀ i < k, P.normal (a + UInt64.ofNat i) = true) :
    P.mapped a k = true := by
  unfold Platform.mapped
  rw [List.all_eq_true]
  intro i hi
  exact h i (List.mem_range.mp hi)

theorem stdinOf_append (tr : List Event) (e : Event) :
    stdinOf (tr ++ [e]) = stdinOf tr ++ e.inBytes := by
  simp [stdinOf]

theorem stdoutOf_append (tr : List Event) (e : Event) :
    stdoutOf (tr ++ [e]) = stdoutOf tr ++ e.outBytes := by
  simp [stdoutOf]

/-- The area's byte `4096 + j` lies at `X17 + 4096 + j`, below the stack's limit, as a number. -/
theorem area_toNat {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {s : State}
    (h : StoreRel P cap gts st s) {j : Nat} (hj : 4096 + j < areaSize cap) :
    (s.x 17 + UInt64.ofNat (4096 + j)).toNat = (s.x 17).toNat + 4096 + j := by
  have hb := h.below
  have := (s.x 18).toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

/-- The loop of `run_readPass` at `H`, from its head with `c` bytes of the block left of `N`, the
`got` bytes before them holding the input's first `got` bytes, which the trace's reads returned.
When the input has fewer than `N` bytes, the run leaves the loop at the end of input, `after H 9`,
with the whole input in the block, every read of the trace, and nothing written.  Otherwise it
reaches the stub of status 64 with nothing written.  No call fails. -/
theorem run_readLoop {K : Kernel} {H e64 e65 rd : UInt64} {fe fl fr : Fin 524288}
    {gr go : Fin 67108864}
    (hc : CodeAt code H [.movz 0 0 0, .bl gr, .cbz 0 fe, .subsReg 31 0 2, .bcond 8 fl,
      .addReg 1 1 0, .subReg 2 2 0, .cbnz 2 fr, .b go])
    (hgr : bField (after H 1) rd = .ok gr) (hfe : cbField (after H 2) (after H 9) = .ok fe)
    (hfl : cbField (after H 4) e65 = .ok fl) (hfr : cbField (after H 7) H = .ok fr)
    (hgo : bField (after H 8) e64 = .ok go)
    (hrd : OpsAt code rd [.ins (.movz 8 63 0), .svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55)
    (h9 : (after H 9).toNat < 2 ^ 55) (h64 : e64.toNat < 2 ^ 55)
    (hok : ∀ k, K.fail k = none) {cap : Nat} {gts : List ValueType} (st : Store Unit)
    (root N : Nat) (hN : root + N ≤ st.mem.pages * 65536) :
    ∀ c (p : Proc) (got : Nat), got + c = N → 0 < c → p.core.pc = H → p.fpcr = fpcrValue →
      p.core.x 2 = UInt64.ofNat c →
      p.core.x 1 = p.core.x 17 + UInt64.ofNat (4096 + (root + got)) →
      stdinOf p.trace = K.input.take got → got ≤ K.input.length → stdoutOf p.trace = [] →
      StoreRel P cap gts (storeBytes st root (K.input.take got)) p.core →
      (K.input.length < N → ∃ p', ProcReach K P code p p' ∧ p'.core.pc = after H 9 ∧
          p'.core.x 2 = UInt64.ofNat (N - K.input.length) ∧
          StoreRel P cap gts (storeBytes st root K.input) p'.core ∧
          stdinOf p'.trace = K.input ∧ stdoutOf p'.trace = [] ∧ p'.fpcr = fpcrValue ∧
          (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 8 → q ≠ 30 → p'.core.x q = p.core.x q) ∧
          p'.core.sp = p.core.sp ∧
          (∀ a : UInt64, (p.core.x 18).toNat ≤ a.toNat → p'.core.mem a = p.core.mem a) ∧
          p'.core.io = p.core.io) ∧
      (N ≤ K.input.length → ∃ p', ProcReach K P code p p' ∧ p'.core.pc = e64 ∧
          stdoutOf p'.trace = [] ∧ p'.fpcr = fpcrValue ∧ p'.core.io = p.core.io) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro p got hgc hc0 hpc hf h2 h1 hin hgot hout hsr
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  rw [(storeBytes_globals st root (K.input.take got)).2.1] at hpg
  have hcapN : root + N ≤ cap * 65536 := Nat.le_trans hN (Nat.mul_le_mul_right _ hpg.2)
  have hc64 : c < 2 ^ 64 := by
    have : cap * 65536 < 2 ^ 64 := by simp only [Nat.reducePow]; omega
    omega
  have hrest : K.rest p.trace = K.input.drop got := by
    unfold Kernel.rest
    rw [hin, List.length_take, Nat.min_eq_left hgot]
  generalize hr : min (K.size p.trace.length + 1) (min c (K.rest p.trace).length) = r
  have hrc : r ≤ c := by rw [← hr]; omega
  have hrl : r ≤ K.input.length - got := by
    rw [← hr, hrest, List.length_drop]
    omega
  have hmap : P.mapped (p.core.x 1) c = true := mapped_of_all P fun i hi => by
    rw [h1, add_ofNat_add, show 4096 + (root + got) + i = 4096 + (root + got + i) by omega]
    exact hsr.mapped _ (by unfold areaSize; omega)
  obtain ⟨p', q1, hf', htr', hmem', hsp', hio', hx', out⟩ := run_readPass P code hc hgr hfe hfl
    hfr hgo hrd hdom h9 h64 hpc hf (hok _) hc64 h2 hr hmap
  have hchunk : (K.rest p.trace).take r = (K.input.drop got).take r := by rw [hrest]
  rw [hchunk] at htr' hmem'
  have h17' : p'.core.x 17 = p.core.x 17 := hx' 17 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have h18' : p'.core.x 18 = p.core.x 18 := hx' 18 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  -- the store and the frame after the read
  have hlen : (K.input.take got).length = got := by rw [List.length_take]; omega
  have hsr' : StoreRel P cap gts (storeBytes st root (K.input.take (got + r))) p'.core := by
    have hw := StoreRel.kernelWrite P ((K.input.drop got).take r) _ p.core (root + got) hsr
      (by
        rw [(storeBytes_globals st root (K.input.take got)).2.1, List.length_take]
        omega)
    have e := storeBytes_append st root (K.input.take got) ((K.input.drop got).take r)
    rw [hlen, ← List.take_add] at e
    rw [← e] at hw
    exact hw.regs h17' h18' (by rw [hmem', h1])
  have hframe : ∀ a : UInt64, (p.core.x 18).toNat ≤ a.toNat → p'.core.mem a = p.core.mem a := by
    intro a ha
    rw [hmem']
    apply writeList_other
    have hb := hsr.below
    have hx1 : (p.core.x 1).toNat = (p.core.x 17).toNat + 4096 + (root + got) := by
      rw [h1]
      exact area_toNat P hsr (by unfold areaSize; omega)
    rw [toNat_sub_le (by unfold areaSize at hb; omega), hx1, List.length_take, List.length_drop]
    unfold areaSize at hb
    omega
  have hstdin' : stdinOf p'.trace = K.input.take (got + r) := by
    rw [htr', stdinOf_append, hin]
    simp [Event.inBytes, List.take_add]
  have hstdout' : stdoutOf p'.trace = [] := by
    rw [htr', stdoutOf_append, hout]
    rfl
  rcases out with ⟨hr0, hpc', hx1', hx2'⟩ | ⟨hrp, hlt, hpc', hx1', hx2'⟩ | ⟨hrp, hrc', hpc'⟩
  · -- a read of 0 bytes: the end of input
    have hend : K.input.length = got := by
      rw [← hr] at hr0
      have : (K.rest p.trace).length = 0 := by omega
      rw [hrest, List.length_drop] at this
      omega
    refine ⟨fun _ => ⟨p', q1, hpc', by rw [hx2', h2]; congr 1; omega, ?_, ?_, hstdout', hf',
      hx', hsp', hframe, hio'⟩, fun h => absurd h (by omega)⟩
    · rw [hr0, Nat.add_zero] at hsr'
      rwa [List.take_of_length_le (by omega)] at hsr'
    · rw [hstdin', hr0, Nat.add_zero, List.take_of_length_le (by omega)]
  · -- a short read: the loop again
    have hih := ih (c - r) (by omega) p' (got + r) (by omega) (by omega) hpc' hf' hx2'
      (by rw [hx1', h1, h17', add_ofNat_add]; congr 2; omega) hstdin' (by omega) hstdout'
      hsr'
    have h18'' : (p.core.x 18).toNat = (p'.core.x 18).toNat := by rw [h18']
    refine ⟨fun hlt' => ?_, fun hge => ?_⟩
    · obtain ⟨p'', q2, hpc'', hx2'', hsr'', hin'', hout'', hf'', hx'', hsp'', hfr'', hio''⟩ :=
        hih.1 hlt'
      exact ⟨p'', q1.trans q2, hpc'', hx2'', hsr'', hin'', hout'', hf'',
        fun q a b c' d e => (hx'' q a b c' d e).trans (hx' q a b c' d e), hsp''.trans hsp',
        fun a ha => (hfr'' a (by rw [← h18'']; exact ha)).trans (hframe a ha), hio''.trans hio'⟩
    · obtain ⟨p'', q2, hpc'', hout'', hf'', hio''⟩ := hih.2 hge
      exact ⟨p'', q1.trans q2, hpc'', hout'', hf'', hio''.trans hio'⟩
  · -- the block is full
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨p', q1, hpc', hstdout', hf', hio'⟩⟩

/-! ## The write loop -/

/-- The part of a pass of the write loop after the call, from the `CBZ` at `after W 3`, with the
write's count `r`, from 1 to the `c` bytes that remain, in X0 and `c` in X2: X1 and X2 step by `r`,
and the run returns to the loop's head `W`. -/
theorem run_writeTail {W e66 : UInt64} {fz fl : Fin 524288} {gb : Fin 67108864}
    (hc : CodeAt code (after W 3) [.cbz 0 fz, .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0,
      .subReg 2 2 0, .b gb])
    (hfl : cbField (after W 5) e66 = .ok fl) (hgb : bField (after W 8) W = .ok gb)
    {s : State} (hpc : s.pc = after W 3) {r c : Nat} (hr0 : 0 < r) (hr : r ≤ c)
    (hc64 : c < 2 ^ 64) (h0 : s.x 0 = UInt64.ofNat r) (h2 : s.x 2 = UInt64.ofNat c) :
    ∃ t, Reach P code s t ∧ t.pc = W ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 1 → q ≠ 2 → t.x q = s.x q) ∧ t.x 1 = s.x 1 + UInt64.ofNat r ∧
      t.x 2 = UInt64.ofNat (c - r) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  have c5 := hc 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c0 c1 c2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c3 c4 c5
  have hr64 : r < 2 ^ 64 := by omega
  let s1 : State := { s with pc := s.pc + 4 }
  have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0)
    (cbz_next P (by rw [h0]; exact ofNat_ne_zero hr0 hr64)) (.refl _)
  have p1 : s1.pc = after W 4 := by show s.pc + 4 = _; rw [hpc, ← after_succ]
  have hhi : CodeAt code (after W 4) [.subsReg 31 0 2, .bcond 8 fl] :=
    CodeAt.cons.mpr ⟨c1, CodeAt.cons.mpr ⟨by rw [after_after]; exact c2,
      fun i hi => absurd hi (by simp)⟩⟩
  obtain ⟨s2, r2, p2, x2, sp2, mem2, io2⟩ := run_hiReg P code (x := 0) (y := 2) hhi
    (by rw [after_after]; exact hfl) p1
  have hnlt : ¬ s1.x 2 < s1.x 0 := by
    show ¬ s.x 2 < s.x 0
    rw [h0, h2, ofNat_lt_ofNat hc64 hr64]
    omega
  rw [if_neg hnlt, after_after] at p2
  obtain ⟨s3, r3, p3, x13, k3, sp3, mem3, io3⟩ := run_setX P code (d := 1) (by decide)
    (by rw [p2]; exact c3) (rfl : LeanExe.A64.exec P (.addReg 1 1 0) s2 = _)
  obtain ⟨s4, r4, p4, x24, k4, sp4, mem4, io4⟩ := run_setX P code (d := 2) (by decide)
    (by rw [p3, p2, ← after_succ]; exact c4) (rfl : LeanExe.A64.exec P (.subReg 2 2 0) s3 = _)
  have p4' : s4.pc = after W 8 := by rw [p4, p3, p2, ← after_succ, ← after_succ]
  let s5 : State := { s4 with pc := s4.pc + sext 26 gb.val * 4 }
  have r5 : Reach P code s4 s5 := reach_exec P code (by rw [p4']; exact c5) rfl (.refl _)
  refine ⟨s5, r1.trans (r2.trans (r3.trans (r4.trans r5))), ?_, by rw [sp4, sp3, sp2],
    by rw [mem4, mem3, mem2], by rw [io4, io3, io2], fun q h1 h2' => ?_, ?_, ?_⟩
  · show s4.pc + sext 26 gb.val * 4 = W
    rw [p4']
    exact bField_target hgb
  · show s4.x q = _
    rw [k4 q h2', k3 q h1, x2 q]
    rfl
  · show s4.x 1 = _
    rw [k4 1 (by decide), x13, x2 1, x2 0]
    show s.x 1 + s.x 0 = _
    rw [h0]
  · show s4.x 2 = _
    rw [x24, k3 2 (by decide), k3 0 (by decide), x2 2, x2 0]
    show s.x 2 - s.x 0 = _
    rw [h0, h2, ofNat_sub_ofNat hr hc64]

/-- The loop of the result's writes at `W`, from its head with `c` bytes from X1 to write, all in
Normal memory: the run leaves the loop at `after W 9` with the bytes of the memory from X1 added to
the trace's output, the memory kept, and the stack pointer, the UART's state, and every register
but X0, X1, X2, X8, and X30 kept.  No call fails. -/
theorem run_writeLoop' {K : Kernel} {W e66 wr : UInt64} {fd fz fl : Fin 524288}
    {gw gb : Fin 67108864}
    (hc : CodeAt code W [.cbz 2 fd, .movz 0 1 0, .bl gw, .cbz 0 fz, .subsReg 31 0 2,
      .bcond 8 fl, .addReg 1 1 0, .subReg 2 2 0, .b gb])
    (hfd : cbField W (after W 9) = .ok fd) (hgw : bField (after W 2) wr = .ok gw)
    (hfl : cbField (after W 5) e66 = .ok fl) (hgb : bField (after W 8) W = .ok gb)
    (hwr : OpsAt code wr [.ins (.movz 8 64 0), .svc, .ins (.ret 30)])
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (h9 : (after W 9).toNat < 2 ^ 55)
    (hok : ∀ k, K.fail k = none) :
    ∀ c (p : Proc), p.core.pc = W → p.fpcr = fpcrValue → p.core.x 2 = UInt64.ofNat c →
      c < 2 ^ 64 → (∀ i < c, P.normal (p.core.x 1 + UInt64.ofNat i) = true) →
      ∃ p', ProcReach K P code p p' ∧ p'.core.pc = after W 9 ∧ p'.fpcr = fpcrValue ∧
        stdoutOf p'.trace = stdoutOf p.trace ++ readList p.core.mem (p.core.x 1) c ∧
        p'.core.mem = p.core.mem ∧ p'.core.sp = p.core.sp ∧ p'.core.io = p.core.io ∧
        (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 8 → q ≠ 30 → p'.core.x q = p.core.x q) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro p hpc hf h2 hc64 hmapc
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · -- nothing left: the CBZ leaves the loop
    have r0 := cbz_taken P code (by rw [hpc]; exact c0) hpc hfd (by rw [h2]; rfl)
    refine ⟨p.goto (after W 9), ProcReach.of_reach' hdom hf r0 h9, rfl, hf, by simp [readList],
      rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  -- the CBZ, MOVZ X0, #1, and BL sysWrite
  let t0 : State := { p.core with pc := p.core.pc + 4 }
  have r0 : Reach P code p.core t0 := reach_exec P code (by rw [hpc]; exact c0)
    (cbz_next P (by rw [h2]; exact ofNat_ne_zero hc0 hc64)) (.refl _)
  have p0 : t0.pc = after W 1 := by show p.core.pc + 4 = _; rw [hpc, after_one]
  obtain ⟨t1, r1, p1, x01, k1, sp1, mem1, io1⟩ :=
    run_movz P code (d := 0) (v := 1) (by decide) (by rw [p0]; exact c1)
  have p1' : t1.pc = after W 2 := by rw [p1, p0, ← after_succ]
  let t2 : State := { t1.setX 30 (t1.pc + 4) with pc := t1.pc + sext 26 gw.val * 4 }
  have r2 : Reach P code p.core t2 :=
    r0.trans (r1.trans (reach_exec P code (by rw [p1']; exact c2) rfl (.refl _)))
  have p2 : t2.pc = wr := by
    show t1.pc + sext 26 gw.val * 4 = wr
    rw [p1']
    exact bField_target hgw
  have h302 : t2.x 30 = after W 3 := by
    rw [State.x_withPc, State.x_setX_same (by decide), p1', ← after_succ]
  have hk2 : ∀ q : Fin 32, q ≠ 0 → q ≠ 30 → t2.x q = p.core.x q := fun q h0 h30 => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h30), k1 q h0]
    rfl
  have hwr0 := hwr 0 (by simp)
  simp only [after_zero, List.getElem_cons_zero] at hwr0
  have q2 : ProcReach K P code p { p with core := t2 } :=
    ProcReach.of_reach' hdom hf r2 (by rw [p2]; exact hdom _ _ hwr0)
  -- the call
  let pp : Proc := { p with core := t2 }
  have hx2 : ((pp.enter (UInt64.ofNat (64 : Fin 65536).val)).core.x 2).toNat = c := by
    rw [Proc.enter_x _ _ (by decide)]
    show (t2.x 2).toNat = c
    rw [hk2 2 (by decide) (by decide), h2, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hc64]
  have hx1 : (pp.enter (UInt64.ofNat (64 : Fin 65536).val)).core.x 1 = p.core.x 1 := by
    rw [Proc.enter_x _ _ (by decide)]
    exact hk2 1 (by decide) (by decide)
  generalize hr : min (K.size p.trace.length + 1) c = r
  have hr0 : 0 < r := by rw [← hr]; omega
  have hrc : r ≤ c := by rw [← hr]; omega
  have hsvc := svc_write (K := K) (P := P) (p := pp.enter (UInt64.ofNat (64 : Fin 65536).val))
    (by rw [Proc.enter_x8]; rfl)
    (by
      rw [Proc.enter_x _ _ (by decide)]
      show (t1.setX 30 (t1.pc + 4)).x 0 = 1
      rw [State.x_setX_ne (by decide), x01]
      rfl)
    (hok _) (by
      rw [hx2, hx1]
      exact mapped_of_all P fun i hi => hmapc i hi)
  have htr2 : pp.trace = p.trace := rfl
  rw [hx2, hx1, Proc.enter_trace, htr2, hr] at hsvc
  have q3 := run_svcCall (K := K) (P := P) (code := code) (p := pp) hwr hdom p2 hsvc
    (by rw [Proc.ret_pc, Proc.enter_pc]; exact add_four_four _)
    (by rw [Proc.ret_x _ _ _ _ (by decide), Proc.enter_x _ _ (by decide)])
    (by show (t2.x 30).toNat < 2 ^ 55; rw [h302]; exact hdom _ _ c3)
  generalize hp3 : ((pp.enter (UInt64.ofNat (64 : Fin 65536).val)).ret (UInt64.ofNat r)
    (pp.enter (UInt64.ofNat (64 : Fin 65536).val)).core.mem
    (.write (readList (pp.enter (UInt64.ofNat (64 : Fin 65536).val)).core.mem (p.core.x 1) r))).goto
      (pp.core.x 30) = p3 at q3
  have p3x : ∀ q : Fin 32, q ≠ 0 → q ≠ 8 → p3.core.x q = t2.x q := fun q h0 h8 => by
    rw [← hp3, Proc.goto_x, Proc.ret_x _ _ _ _ h0, Proc.enter_x _ _ h8]
  have hmem2 : t2.mem = p.core.mem := by
    show (t1.setX 30 (t1.pc + 4)).mem = _
    rw [State.setX_mem, mem1]
  have p3mem : p3.core.mem = p.core.mem := by
    rw [← hp3, Proc.goto_mem, Proc.ret_mem, Proc.enter_mem]
    exact hmem2
  have p3sp : p3.core.sp = p.core.sp := by
    rw [← hp3, Proc.goto_sp, Proc.ret_sp, Proc.enter_sp]
    show (t1.setX 30 (t1.pc + 4)).sp = _
    rw [State.setX_sp, sp1]
  have p3io : p3.core.io = p.core.io := by
    rw [← hp3, Proc.goto_io, Proc.ret_io, Proc.enter_io]
    show (t1.setX 30 (t1.pc + 4)).io = _
    rw [State.setX_io, io1]
  have p3out : stdoutOf p3.trace = stdoutOf p.trace ++ readList p.core.mem (p.core.x 1) r := by
    rw [← hp3, Proc.goto_trace, Proc.ret_trace, Proc.enter_trace, stdoutOf_append, htr2,
      Proc.enter_mem]
    show stdoutOf p.trace ++ readList t2.mem _ r = _
    rw [hmem2]
  have p3f : p3.fpcr = fpcrValue := by
    rw [← hp3, Proc.goto_fpcr, Proc.ret_fpcr, Proc.enter_fpcr]
    exact hf
  -- the rest of the pass and the loop
  have hct : CodeAt code (after W 3) [.cbz 0 fz, .subsReg 31 0 2, .bcond 8 fl, .addReg 1 1 0,
      .subReg 2 2 0, .b gb] := (CodeAt.split code (l1 := [.cbz 2 fd, .movz 0 1 0, .bl gw]) hc rfl).2
  obtain ⟨t, rt, pt, spt, memt, iot, kt, x1t, x2t⟩ := run_writeTail P code hct hfl hgb
    (s := p3.core) (by rw [← hp3, Proc.goto_pc]; exact h302) hr0 hrc hc64
    (by rw [← hp3, Proc.goto_x, Proc.ret_x0])
    (by rw [p3x 2 (by decide) (by decide), hk2 2 (by decide) (by decide), h2])
  have q4 := ProcReach.of_reach' (K := K) hdom p3f rt
    (by rw [pt]; exact hdom _ _ (by simpa [after_zero] using c0))
  have hx1t : t.x 1 = p.core.x 1 + UInt64.ofNat r := by
    rw [x1t, p3x 1 (by decide) (by decide), hk2 1 (by decide) (by decide)]
  obtain ⟨p', q5, hpc', hf', hout', hmem', hsp', hio', hx'⟩ := ih (c - r) (by omega)
    { p3 with core := t } pt p3f x2t (by omega) (fun i hi => by
      show P.normal (t.x 1 + UInt64.ofNat i) = true
      rw [hx1t, add_ofNat_add]
      exact hmapc _ (by omega))
  refine ⟨p', q2.trans (q3.trans (q4.trans q5)), hpc', hf', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout']
    show stdoutOf p3.trace ++ readList t.mem (t.x 1) (c - r) = _
    rw [p3out, memt, p3mem, hx1t, List.append_assoc, ← readList_add, Nat.add_sub_cancel' hrc]
  · rw [hmem']
    show t.mem = _
    rw [memt, p3mem]
  · rw [hsp']
    show t.sp = _
    rw [spt, p3sp]
  · rw [hio']
    show t.io = _
    rw [iot, p3io]
  · intro q h0 h1 h2' h8 h30
    rw [hx' q h0 h1 h2' h8 h30]
    show t.x q = _
    rw [kt q h1 h2', p3x q h0 h8, hk2 q h0 h30]

end LeanExe.A64
