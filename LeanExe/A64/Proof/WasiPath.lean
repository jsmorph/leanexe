module

public import LeanExe.A64.Proof.WasiStubs
public import LeanExe.A64.WasiFiles

@[expose] public section

/-!
`run_zeroScan` and `run_pathCopy` follow, in the program's model, the two loops of the stub of
`path_open` over the path's bytes in guest memory, `zeroScan` and `pathCopy` of
`LeanExe/A64/WasiFiles.lean`.  Each generator starts with `guestAddr`, which `run_guestAddr`
follows to the guest's address `X17 + 4096 + X2` in X9, and each loop's lemma holds by induction
on the number of bytes that remain, with X9 at the next byte.  `run_zeroLoop` counts the bytes
that remain in X10 and reaches `bad` at the first zero byte, and `run_pathLoop` counts them in X12
and stores each byte at the destination in X10.

The copy reads each byte of the source after it has stored the bytes before it, so
`run_pathLoop` requires that no byte that it reads lies at a destination byte that an earlier pass
wrote.  `run_pathCopy` derives that requirement from a source that ends at or below the start of
the scratch's path buffer at offset 1,080 and a buffer whose 4,096 bytes lie below `2^64`.  The
memory after the copy is `writeList` of the bytes that `readList` reads from the memory before it,
followed by the terminating zero (`writeList_concat`).
-/

namespace LeanExe.A64

/-! ## The generators' instructions -/

theorem zeroScan_ok {a bad : UInt64} {is : List Instr} (hg : zeroScan a bad = .ok is) :
    ∃ g1 g2 g3, cbField (after a 4) (after a 10) = .ok g1 ∧ cbField (after a 6) bad = .ok g2 ∧
      bField (after a 9) (after a 4) = .ok g3 ∧
      is = [.addReg 9 17 2, .addImm 9 9 4095, .addImm 9 9 1, .orrReg 10 31 3, .cbz 10 g1,
        .ldrb 12 9 0, .cbz 12 g2, .addImm 9 9 1, .subImm 10 10 1, .b g3] := by
  unfold zeroScan at hg
  cases h1 : cbField (after a 4) (after a 10) with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h2 : cbField (after a 6) bad with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g2 =>
  cases h3 : bField (after a 9) (after a 4) with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok g3 =>
  simp only [h1, h2, h3, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g2, g3, rfl, rfl, rfl, hg.symm⟩

theorem pathCopy_ok {a : UInt64} {is : List Instr} (hg : pathCopy a = .ok is) :
    ∃ g1 g2, cbField (after a 5) (after a 12) = .ok g1 ∧ bField (after a 11) (after a 5) = .ok g2 ∧
      is = [.addReg 9 17 2, .addImm 9 9 4095, .addImm 9 9 1, .addImm 10 20 1080, .orrReg 12 31 3,
        .cbz 12 g1, .ldrb 13 9 0, .strb 13 10 0, .addImm 9 9 1, .addImm 10 10 1, .subImm 12 12 1,
        .b g2, .strb 31 10 0] := by
  unfold pathCopy at hg
  cases h1 : cbField (after a 5) (after a 12) with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h2 : bField (after a 11) (after a 5) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g2 =>
  simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g2, rfl, rfl, hg.symm⟩

/-! ## Bytes and addresses -/

theorem guestAddr_val (x y : UInt64) :
    x + y + UInt64.ofNat (4095 : Fin 4096).val + UInt64.ofNat (1 : Fin 4096).val =
      x + UInt64.ofNat 4096 + y := by
  show x + y + UInt64.ofNat 4095 + UInt64.ofNat 1 = _
  have := x.toNat_lt
  have := y.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMod] at *
  omega

theorem byte_toUInt64_eq_zero {b : UInt8} : b.toUInt64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat] at this
    exact UInt8.toNat_inj.mp this
  · intro h
    rw [h]
    rfl

/-- A store at `b` leaves the `n` bytes from `a` when none of them lies at `b`. -/
theorem readList_store8 (m : UInt64 → UInt8) (b : UInt64) (v : UInt8) :
    ∀ (a : UInt64) (n : Nat), (∀ j < n, a + UInt64.ofNat j ≠ b) →
      readList (store8 m b v) a n = readList m a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
    have h0 := h 0 (by omega)
    rw [add_ofNat_zero] at h0
    rw [readList, readList, store8_other _ _ _ _ h0, readList_store8 m b v (a + 1) n fun j hj => by
      rw [LeanExe.Linux.succ_ofNat]
      exact h (j + 1) (by omega)]

/-- Writing `l ++ [b]` from `a` writes `l` and then stores `b` at the byte after it. -/
theorem writeList_concat (b : UInt8) :
    ∀ (m : UInt64 → UInt8) (a : UInt64) (l : List UInt8),
      writeList m a (l ++ [b]) = store8 (writeList m a l) (a + UInt64.ofNat l.length) b
  | m, a, [] => by
    rw [List.length_nil, add_ofNat_zero]
    rfl
  | m, a, x :: l => by
    rw [List.cons_append, writeList, writeList, writeList_concat b (store8 m a x) (a + 1) l,
      List.length_cons, LeanExe.Linux.succ_ofNat]

/-- Byte `j` of a source that ends at or below a destination `D`, whose 4,096 bytes lie below
`2^64`, differs from the destination's byte `i`. -/
theorem add_ofNat_ne_add_ofNat {S D : UInt64} {n j i : Nat} (hj : j < n) (hi : i < 4096)
    (hsep : S.toNat + n ≤ D.toNat) (hwrap : D.toNat + 4096 ≤ 2 ^ 64) :
    S + UInt64.ofNat j ≠ D + UInt64.ofNat i := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at this hwrap
  omega

/-! ## The runs -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The guest's address `X17 + 4096 + Xp` in X`d`. -/
theorem run_guestAddr {a : UInt64} {d p : Fin 32} (hd : d.val < 31)
    (hcode : CodeAt code a (guestAddr d p)) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = after a 3 ∧ t.x d = s.x 17 + UInt64.ofNat 4096 + s.x p ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp [guestAddr])
  have c1 := hcode 1 (by simp [guestAddr])
  have c2 := hcode 2 (by simp [guestAddr])
  simp only [guestAddr, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := d) (n := 17)
    (m := p) hd (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := d) (n := d)
    (imm := 4095) hd hd (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addImm P code (s := u2) (d := d) (n := d)
    (imm := 1) hd hd (by rw [q2]; exact c2)
  refine ⟨u3, r1.trans (r2.trans r3), by rw [p3, q2, ← after_succ], ?_,
    fun q hq => by rw [k3 q hq, k2 q hq, k1 q hq], by rw [sp3, sp2, sp1], by rw [m3, m2, m1],
    by rw [io3, io2, io1]⟩
  rw [x3, x2, x1]
  exact guestAddr_val _ _

/-- The loop of `zeroScan` from its head at `h`, with X9 at the next byte and the `c` bytes that
remain in X10: `bad` when one of the `c` bytes from X9 is zero, and `after h 6` otherwise, with
X9, X10, and X12 changed. -/
theorem run_zeroLoop {h bad : UInt64} {g1 g2 : Fin 524288} {g3 : Fin 67108864}
    (hc : CodeAt code h [.cbz 10 g1, .ldrb 12 9 0, .cbz 12 g2, .addImm 9 9 1, .subImm 10 10 1,
      .b g3])
    (hg1 : cbField h (after h 6) = .ok g1) (hg2 : cbField (after h 2) bad = .ok g2)
    (hg3 : bField (after h 5) h = .ok g3) :
    ∀ (c : Nat) (s : State), c < 2 ^ 64 → s.pc = h → s.x 10 = UInt64.ofNat c →
      (∀ k < c, P.normal (s.x 9 + UInt64.ofNat k) = true) →
      ∃ t, Reach P code s t ∧
        t.pc = (if (0 : UInt8) ∈ readList s.mem (s.x 9) c then bad else after h 6) ∧
        (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → t.x q = s.x q) ∧
        t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  have c5 := hc 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5
  intro c
  induction c with
  | zero =>
    intro s _ hpc h10 _
    obtain ⟨t, r, p, k, sp, m, io⟩ := step_cbz P code (s := s) (r := 10) (target := after h 6)
      (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hg1)
    refine ⟨t, r, ?_, fun q _ _ _ => k q, sp, m, io⟩
    rw [p, ite_eq_left (by rw [h10]; rfl), ite_eq_right (by simp [readList])]
  | succ c ih =>
    intro s hc64 hpc h10 hmap
    obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbz P code (s := s) (r := 10)
      (target := after h 6) (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hg1)
    rw [ite_eq_right (by rw [h10]; exact ofNat_succ_ne_zero hc64), hpc, ← after_one] at p1
    have hm0 : P.normal (u1.x 9 + UInt64.ofNat (0 : Fin 4096).val) = true := by
      rw [k1]
      exact hmap 0 (by omega)
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_setX P code (s := u1) (d := 12)
      (by decide) (by rw [p1]; exact c1) (exec_ldrb_base P (t := 12) (by decide) hm0)
    have hb2 : u2.x 12 = (s.mem (s.x 9)).toUInt64 := by
      rw [x2, m1, k1, show UInt64.ofNat (0 : Fin 4096).val = UInt64.ofNat 0 from rfl,
        add_ofNat_zero]
    have q2 : u2.pc = after h 2 := by rw [p2, p1, ← after_succ]
    obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_cbz P code (s := u2) (r := 12) (target := bad)
      (by rw [q2]; exact c2) (by rw [q2]; exact cbField_target hg2)
    by_cases hb : s.mem (s.x 9) = 0
    · rw [ite_eq_left (by rw [hb2, hb]; rfl)] at p3
      refine ⟨u3, r1.trans (r2.trans r3), ?_, fun q _ _ h12 => by rw [k3, k2 q h12, k1],
        by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1]⟩
      rw [p3, ite_eq_left (by rw [readList, hb]; simp)]
    · rw [ite_eq_right (by rw [hb2]; exact fun e => hb (byte_toUInt64_eq_zero.mp e)), q2,
        ← after_succ] at p3
      obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addImm P code (s := u3) (d := 9) (n := 9)
        (imm := 1) (by decide) (by decide) (by rw [p3]; exact c3)
      have q4 : u4.pc = after h 4 := by rw [p4, p3, ← after_succ]
      obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_setX P code (s := u4) (d := 10)
        (by decide) (by rw [q4]; exact c4)
        (exec_subImm_x P (d := 10) (n := 10) (imm := 1) (by decide) (by decide))
      have q5 : u5.pc = after h 5 := by rw [p5, q4, ← after_succ]
      obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := step_b P code (s := u5) (target := h)
        (by rw [q5]; exact c5) (by rw [q5]; exact bField_target hg3)
      have x4' : u4.x 9 = u3.x 9 + 1 := x4
      have h9 : u6.x 9 = s.x 9 + 1 := by rw [k6, k5 9 (by decide), x4', k3, k2 9 (by decide), k1]
      have h10' : u6.x 10 = UInt64.ofNat c := by
        rw [k6, x5, k4 10 (by decide), k3, k2 10 (by decide), k1, h10]
        exact ofNat_succ_toUInt64 c hc64
      obtain ⟨t, rt, pt, kt, spt, mt, iot⟩ := ih u6 (by omega) p6 h10' fun k hk => by
        rw [h9, LeanExe.Linux.succ_ofNat]
        exact hmap (k + 1) (by omega)
      rw [m6, m5, m4, m3, m2, m1, h9] at pt
      have hiff : (0 : UInt8) ∈ readList s.mem (s.x 9) (c + 1) ↔
          (0 : UInt8) ∈ readList s.mem (s.x 9 + 1) c := by
        rw [readList, List.mem_cons]
        exact ⟨fun e => e.resolve_left fun e0 => hb e0.symm, Or.inr⟩
      refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans rt))))), ?_,
        fun q h9' h10'' h12 => by
          rw [kt q h9' h10'' h12, k6, k5 q h10'', k4 q h9', k3, k2 q h12, k1],
        by rw [spt, sp6, sp5, sp4, sp3, sp2, sp1], by rw [mt, m6, m5, m4, m3, m2, m1],
        by rw [iot, io6, io5, io4, io3, io2, io1]⟩
      rw [pt]
      exact if_congr hiff.symm rfl rfl

/-- The run of `zeroScan` from its first word: `bad` when one of the `n` bytes from the guest's
address `X17 + 4096 + X2` is zero, `n` in X3, and the next word after it otherwise, with X9, X10,
and X12 changed. -/
theorem run_zeroScan {a bad : UInt64} {is : List Instr} (hg : zeroScan a bad = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < (s.x 3).toNat,
      P.normal (s.x 17 + UInt64.ofNat 4096 + s.x 2 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧
      t.pc = (if (0 : UInt8) ∈ readList s.mem (s.x 17 + UInt64.ofNat 4096 + s.x 2) (s.x 3).toNat
        then bad else after a 10) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨g1, g2, g3, hg1, hg2, hg3, rfl⟩ := zeroScan_ok hg
  have c3 := hcode 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c3
  have cs := CodeAt.split code (n := 4)
    (l1 := [.addReg 9 17 2, .addImm 9 9 4095, .addImm 9 9 1, .orrReg 10 31 3])
    (l2 := [.cbz 10 g1, .ldrb 12 9 0, .cbz 12 g2, .addImm 9 9 1, .subImm 10 10 1, .b g3])
    hcode rfl
  have cg := CodeAt.split code (n := 3) (l1 := guestAddr 9 2) (l2 := [.orrReg 10 31 3]) cs.1 rfl
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_guestAddr P code (d := 9) (p := 2)
    (by decide) cg.1 hpc
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_mov P code (s := u1) (d := 10) (m := 3)
    (by decide) (by rw [p1]; exact c3)
  have q2 : u2.pc = after a 4 := by rw [p2, p1, ← after_succ]
  obtain ⟨t, rt, pt, kt, spt, mt, iot⟩ := run_zeroLoop P code cs.2
    (by rw [after_after]; exact hg1) (by rw [after_after]; exact hg2)
    (by rw [after_after]; exact hg3) (s.x 3).toNat u2 (s.x 3).toNat_lt q2
    (by rw [x2, k1 3 (by decide), UInt64.ofNat_toNat])
    (fun k hk => by rw [k2 9 (by decide), x1]; exact hmap k hk)
  rw [m2, m1, k2 9 (by decide), x1, after_after] at pt
  exact ⟨t, r1.trans (r2.trans rt), pt,
    fun q h9 h10 h12 => by rw [kt q h9 h10 h12, k2 q h10, k1 q h9], by rw [spt, sp2, sp1],
    by rw [mt, m2, m1], by rw [iot, io2, io1]⟩

/-- The loop of `pathCopy` from its head at `h`, with X9 at the next source byte, X10 at the next
destination byte, and the `c` bytes that remain in X12: the `c` bytes from X9 written from X10,
X10 moved past them, and the next word after the loop, `after h 7`, with X9, X10, X12, and X13
changed.  The last hypothesis requires that no source byte that the loop reads lies at a
destination byte that it wrote before. -/
theorem run_pathLoop {h : UInt64} {g1 : Fin 524288} {g2 : Fin 67108864}
    (hc : CodeAt code h [.cbz 12 g1, .ldrb 13 9 0, .strb 13 10 0, .addImm 9 9 1,
      .addImm 10 10 1, .subImm 12 12 1, .b g2])
    (hg1 : cbField h (after h 7) = .ok g1) (hg2 : bField (after h 6) h = .ok g2)
    (hU : P.normal P.uart = false) :
    ∀ (c : Nat) (s : State), c < 2 ^ 64 → s.pc = h → s.x 12 = UInt64.ofNat c →
      (∀ k < c, P.normal (s.x 9 + UInt64.ofNat k) = true) →
      (∀ k < c, P.normal (s.x 10 + UInt64.ofNat k) = true) →
      (∀ j < c, ∀ i < j, s.x 9 + UInt64.ofNat j ≠ s.x 10 + UInt64.ofNat i) →
      ∃ t, Reach P code s t ∧ t.pc = after h 7 ∧ t.x 10 = s.x 10 + UInt64.ofNat c ∧
        (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → t.x q = s.x q) ∧
        t.sp = s.sp ∧ t.io = s.io ∧
        t.mem = writeList s.mem (s.x 10) (readList s.mem (s.x 9) c) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  have c5 := hc 5 (by simp)
  have c6 := hc 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5 c6
  intro c
  induction c with
  | zero =>
    intro s _ hpc h12 _ _ _
    obtain ⟨t, r, p, k, sp, m, io⟩ := step_cbz P code (s := s) (r := 12) (target := after h 7)
      (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hg1)
    refine ⟨t, r, by rw [p, ite_eq_left (by rw [h12]; rfl)], by rw [k, add_ofNat_zero],
      fun q _ _ _ _ => k q, sp, io, ?_⟩
    rw [m]
    rfl
  | succ c ih =>
    intro s hc64 hpc h12 hsrc hdst hsep
    obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbz P code (s := s) (r := 12)
      (target := after h 7) (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hg1)
    rw [ite_eq_right (by rw [h12]; exact ofNat_succ_ne_zero hc64), hpc, ← after_one] at p1
    have hm0 : P.normal (u1.x 9 + UInt64.ofNat (0 : Fin 4096).val) = true := by
      rw [k1]
      exact hsrc 0 (by omega)
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_setX P code (s := u1) (d := 13)
      (by decide) (by rw [p1]; exact c1) (exec_ldrb_base P (t := 13) (by decide) hm0)
    have hbyte : (u2.x 13).toUInt8 = s.mem (s.x 9) := by
      rw [x2, m1, k1, show UInt64.ofNat (0 : Fin 4096).val = UInt64.ofNat 0 from rfl,
        add_ofNat_zero, toUInt8_toUInt64']
    have q2 : u2.pc = after h 2 := by rw [p2, p1, ← after_succ]
    have hd0 : P.normal (s.x 10) = true := by
      have := hdst 0 (by omega)
      rwa [add_ofNat_zero] at this
    obtain ⟨u3, r3, p3, k3, sp3, io3, m3⟩ := step_strb P code (s := u2) (t := 13) (n := 10)
      (imm := 0) (k := 0) (addr := s.x 10) (by decide) (by rw [q2]; exact c2) rfl
      (by rw [k2 10 (by decide), k1, add_ofNat_zero]) hd0 hU
    have q3 : u3.pc = after h 3 := by rw [p3, q2, ← after_succ]
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addImm P code (s := u3) (d := 9) (n := 9)
      (imm := 1) (by decide) (by decide) (by rw [q3]; exact c3)
    have q4 : u4.pc = after h 4 := by rw [p4, q3, ← after_succ]
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_addImm P code (s := u4) (d := 10)
      (n := 10) (imm := 1) (by decide) (by decide) (by rw [q4]; exact c4)
    have q5 : u5.pc = after h 5 := by rw [p5, q4, ← after_succ]
    obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_setX P code (s := u5) (d := 12)
      (by decide) (by rw [q5]; exact c5)
      (exec_subImm_x P (d := 12) (n := 12) (imm := 1) (by decide) (by decide))
    have q6 : u6.pc = after h 6 := by rw [p6, q5, ← after_succ]
    obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_b P code (s := u6) (target := h)
      (by rw [q6]; exact c6) (by rw [q6]; exact bField_target hg2)
    have x4' : u4.x 9 = u3.x 9 + 1 := x4
    have x5' : u5.x 10 = u4.x 10 + 1 := x5
    have h9 : u7.x 9 = s.x 9 + 1 := by
      rw [k7, k6 9 (by decide), k5 9 (by decide), x4', k3, k2 9 (by decide), k1]
    have h10 : u7.x 10 = s.x 10 + 1 := by
      rw [k7, k6 10 (by decide), x5', k4 10 (by decide), k3, k2 10 (by decide), k1]
    have h12' : u7.x 12 = UInt64.ofNat c := by
      rw [k7, x6, k5 12 (by decide), k4 12 (by decide), k3, k2 12 (by decide), k1, h12]
      exact ofNat_succ_toUInt64 c hc64
    have hmem : u7.mem = store8 s.mem (s.x 10) (s.mem (s.x 9)) := by
      rw [m7, m6, m5, m4, m3, hbyte, m2, m1]
    obtain ⟨t, rt, pt, xt, kt, spt, iot, mt⟩ := ih u7 (by omega) p7 h12'
      (fun k hk => by
        rw [h9, LeanExe.Linux.succ_ofNat]
        exact hsrc (k + 1) (by omega))
      (fun k hk => by
        rw [h10, LeanExe.Linux.succ_ofNat]
        exact hdst (k + 1) (by omega))
      (fun j hj i hi => by
        rw [h9, h10, LeanExe.Linux.succ_ofNat, LeanExe.Linux.succ_ofNat]
        exact hsep (j + 1) (by omega) (i + 1) (by omega))
    have hread : readList (store8 s.mem (s.x 10) (s.mem (s.x 9))) (s.x 9 + 1) c =
        readList s.mem (s.x 9 + 1) c :=
      readList_store8 _ _ _ _ _ fun j hj => by
        have := hsep (j + 1) (by omega) 0 (by omega)
        rwa [add_ofNat_zero, ← LeanExe.Linux.succ_ofNat] at this
    refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans rt)))))),
      pt, by rw [xt, h10, LeanExe.Linux.succ_ofNat],
      fun q h9' h10' h12'' h13 => by
        rw [kt q h9' h10' h12'' h13, k7, k6 q h12'', k5 q h10', k4 q h9', k3, k2 q h13, k1],
      by rw [spt, sp7, sp6, sp5, sp4, sp3, sp2, sp1],
      by rw [iot, io7, io6, io5, io4, io3, io2, io1], ?_⟩
    rw [mt, hmem, h9, h10, hread, readList, writeList]

/-- The run of `pathCopy` from its first word: the `n` bytes from the guest's address
`X17 + 4096 + X2`, `n` in X3, and a zero written to the scratch's path buffer 1,080 bytes above
X20, and the next word after it, with X9, X10, X12, and X13 changed.  `hsep` places the source at
or below the start of the buffer and `hwrap` the buffer's 4,096 bytes below `2^64`, so the copy
reads the bytes that the memory held before it. -/
theorem run_pathCopy {a : UInt64} {is : List Instr} (hg : pathCopy a = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a)
    (hn : (s.x 3).toNat < 4096)
    (hsrc : ∀ k < (s.x 3).toNat,
      P.normal (s.x 17 + UInt64.ofNat 4096 + s.x 2 + UInt64.ofNat k) = true)
    (hdst : ∀ k ≤ (s.x 3).toNat, P.normal (s.x 20 + UInt64.ofNat (1080 + k)) = true)
    (hU : P.normal P.uart = false)
    (hsep : (s.x 17 + UInt64.ofNat 4096 + s.x 2).toNat + (s.x 3).toNat ≤
      (s.x 20 + UInt64.ofNat 1080).toNat)
    (hwrap : (s.x 20 + UInt64.ofNat 1080).toNat + 4096 ≤ 2 ^ 64) :
    ∃ t, Reach P code s t ∧ t.pc = after a 13 ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = writeList s.mem (s.x 20 + UInt64.ofNat 1080)
        (readList s.mem (s.x 17 + UInt64.ofNat 4096 + s.x 2) (s.x 3).toNat ++ [0]) := by
  obtain ⟨g1, g2, hg1, hg2, rfl⟩ := pathCopy_ok hg
  have c3 := hcode 3 (by simp)
  have c4 := hcode 4 (by simp)
  have c12 := hcode 12 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c3 c4 c12
  have cs := CodeAt.split code (n := 5)
    (l1 := [.addReg 9 17 2, .addImm 9 9 4095, .addImm 9 9 1, .addImm 10 20 1080, .orrReg 12 31 3])
    (l2 := [.cbz 12 g1, .ldrb 13 9 0, .strb 13 10 0, .addImm 9 9 1, .addImm 10 10 1,
      .subImm 12 12 1, .b g2, .strb 31 10 0]) hcode rfl
  have cl := CodeAt.split code (n := 7)
    (l1 := [.cbz 12 g1, .ldrb 13 9 0, .strb 13 10 0, .addImm 9 9 1, .addImm 10 10 1,
      .subImm 12 12 1, .b g2]) (l2 := [.strb 31 10 0]) cs.2 rfl
  have cg := CodeAt.split code (n := 3) (l1 := guestAddr 9 2)
    (l2 := [.addImm 10 20 1080, .orrReg 12 31 3]) cs.1 rfl
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_guestAddr P code (d := 9) (p := 2)
    (by decide) cg.1 hpc
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 10) (n := 20)
    (imm := 1080) (by decide) (by decide) (by rw [p1]; exact c3)
  have q2 : u2.pc = after a 4 := by rw [p2, p1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_mov P code (s := u2) (d := 12) (m := 3)
    (by decide) (by rw [q2]; exact c4)
  have q3 : u3.pc = after a 5 := by rw [p3, q2, ← after_succ]
  have hS : u3.x 9 = s.x 17 + UInt64.ofNat 4096 + s.x 2 := by
    rw [k3 9 (by decide), k2 9 (by decide), x1]
  have x2' : u2.x 10 = u1.x 20 + UInt64.ofNat 1080 := x2
  have hD : u3.x 10 = s.x 20 + UInt64.ofNat 1080 := by
    rw [k3 10 (by decide), x2', k1 20 (by decide)]
  obtain ⟨w, rl, pw, xw, kw, spw, iow, mw⟩ := run_pathLoop P code cl.1
    (by rw [after_after]; exact hg1) (by rw [after_after]; exact hg2) hU (s.x 3).toNat u3
    (s.x 3).toNat_lt q3 (by rw [x3, k2 3 (by decide), k1 3 (by decide), UInt64.ofNat_toNat])
    (fun k hk => by rw [hS]; exact hsrc k hk)
    (fun k hk => by rw [hD, add_ofNat_add]; exact hdst k (by omega))
    (fun j hj i hi => by
      rw [hS, hD]
      exact add_ofNat_ne_add_ofNat hj (by omega) hsep hwrap)
  have hz : (w.x 31).toUInt8 = 0 := (congrArg UInt64.toUInt8 (x31 w)).trans rfl
  obtain ⟨u, ru, pu, ku, spu, iou, mu⟩ := step_strb P code (s := w) (t := 31) (n := 10)
    (imm := 0) (k := 0) (addr := s.x 20 + UInt64.ofNat 1080 + UInt64.ofNat (s.x 3).toNat)
    (by decide) (by rw [pw, after_after]; exact c12) rfl (by rw [xw, hD, add_ofNat_zero])
    (by rw [add_ofNat_add]; exact hdst _ (Nat.le_refl _)) hU
  refine ⟨u, r1.trans (r2.trans (r3.trans (rl.trans ru))),
    by rw [pu, pw, after_after, ← after_succ],
    fun q h9 h10 h12 h13 => by rw [ku, kw q h9 h10 h12 h13, k3 q h12, k2 q h10, k1 q h9],
    by rw [spu, spw, sp3, sp2, sp1], by rw [iou, iow, io3, io2, io1], ?_⟩
  rw [mu, hz, mw, hS, hD, m3, m2, m1, writeList_concat, readList_length]

end LeanExe.A64
