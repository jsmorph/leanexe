import LeanExe.A64.Proof.WasiStubs
import LeanExe.A64.WasiClocks

/-!
The runs of the stubs of `LeanExe/A64/WasiClocks.lean` in the program's model, between the calls
that they make.  `clockStub_ok`, `randomStub_ok`, and `errorTail_ok` unpack the generators.
`run_errorTail` returns the errno of a negated error number in X0 or reaches the trap stub.

`run_clockHead` makes the checks of `clock_time_get` before its call: the trap stub for a clock
above 3 or a pointer above the area's first word, errno 8 for clocks 2 and 3, and otherwise the
call's setup with the return address in X19.  `run_clockCall` sets X20 to the scratch, clears the
timespec, and sets X1 to its address and X8 to `clock_gettime`.  `run_clockTime` handles the
result: the time stored at the guest's pointer with errno 0, errno 61, the trap stub, or an
errno through `run_errorTail`.

`run_randomHead` makes the checks of `random_get`: the trap stub for a buffer beyond the memory,
errno 0 for a buffer of no byte, and otherwise the loop's registers, the address of the buffer in
X20 and its length in X21.  `run_randomCall` sets the arguments of `getrandom` from them, and
`run_randomResult` handles a result: the error tail above the count, the trap stub for 0, errno 0
when no byte remains, and the next pass otherwise.
-/

namespace LeanExe.A64

open Wasm

/-! ## The generators' parts -/

theorem errorTail_ok {a tr en : UInt64} {is : List Instr} (hg : errorTail a tr en = .ok is) :
    ∃ g1 g2, cbField (after a 2) tr = .ok g1 ∧ bField (after a 4) en = .ok g2 ∧
      is = [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g1, .orrReg 0 31 12, .bl g2,
        .ret 19] := by
  unfold errorTail at hg
  cases h1 : cbField (after a 2) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h2 : bField (after a 4) en with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g2 =>
  simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g2, rfl, rfl, hg.symm⟩

/-- The instructions of `clockStub` from its call's result on, with the error tail. -/
def clockTimeCode (g18 g26 g32 g40 : Fin 524288) (g42 : Fin 67108864) : List Instr :=
  [.cbnz 0 g18, .ldr 9 20 130, .ldr 10 20 131] ++ movImm 11 999999999 ++
    [.subsReg 31 10 11, .bcond 8 g26, .addImm 11 11 1, .subReg 12 31 10, .subImm 12 12 1,
      .udiv 12 12 11, .subsReg 31 9 12, .bcond 8 g32, .madd 9 9 11 10, .addReg 13 17 2,
      .str 9 13 512, .movz 0 0 0, .ret 19, .movz 0 61 0, .ret 19, .subReg 12 31 0,
      .subsImm 31 12 4095, .bcond 8 g40, .orrReg 0 31 12, .bl g42, .ret 19]

theorem clockStub_ok {a svc tr en : UInt64} {scratch : Nat} {is : List Instr}
    (hg : clockStub a svc tr en scratch = .ok is) :
    ∃ (g1 g4 g6 g18 g26 g32 g40 : Fin 524288) (gs g42 : Fin 67108864),
      cbField (after a 1) tr = .ok g1 ∧ cbField (after a 4) tr = .ok g4 ∧
      cbField (after a 6) (after a 46) = .ok g6 ∧ bField (after a 17) svc = .ok gs ∧
      cbField (after a 18) (after a 40) = .ok g18 ∧ cbField (after a 26) tr = .ok g26 ∧
      cbField (after a 32) (after a 38) = .ok g32 ∧ cbField (after a 42) tr = .ok g40 ∧
      bField (after a 44) en = .ok g42 ∧
      is = [.subsImm 31 0 3, .bcond 8 g1, .ldr 9 17 0, .subsReg 31 2 9, .bcond 8 g4,
          .subsImm 31 0 1, .bcond 8 g6, .orrReg 19 31 30] ++
        (movImm 20 (UInt64.ofNat scratch) ++ [.addReg 20 17 20, .str 31 20 130,
          .str 31 20 131, .addImm 1 20 1040, .movz 8 113 0]) ++ [.bl gs] ++
        clockTimeCode g18 g26 g32 g40 g42 ++ [.movz 0 8 0, .ret 30] := by
  unfold clockStub at hg
  cases h1 : cbField (after a 1) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h4 : cbField (after a 4) tr with
  | error err => simp [h1, h4, bind, Except.bind] at hg
  | ok g4 =>
  cases h6 : cbField (after a 6) (after a 46) with
  | error err => simp [h1, h4, h6, bind, Except.bind] at hg
  | ok g6 =>
  cases hs : bField (after a 17) svc with
  | error err => simp [h1, h4, h6, hs, bind, Except.bind] at hg
  | ok gs =>
  cases h18 : cbField (after a 18) (after a 40) with
  | error err => simp [h1, h4, h6, hs, h18, bind, Except.bind] at hg
  | ok g18 =>
  cases h26 : cbField (after a 26) tr with
  | error err => simp [h1, h4, h6, hs, h18, h26, bind, Except.bind] at hg
  | ok g26 =>
  cases h32 : cbField (after a 32) (after a 38) with
  | error err => simp [h1, h4, h6, hs, h18, h26, h32, bind, Except.bind] at hg
  | ok g32 =>
  cases ht : errorTail (after a 40) tr en with
  | error err => simp [h1, h4, h6, hs, h18, h26, h32, ht, bind, Except.bind] at hg
  | ok tail =>
  obtain ⟨g40, g42, h40, h42, rfl⟩ := errorTail_ok ht
  simp only [h1, h4, h6, hs, h18, h26, h32, ht, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  rw [after_after] at h40 h42
  refine ⟨g1, g4, g6, g18, g26, g32, g40, gs, g42, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h40, h42,
    ?_⟩
  rw [← hg]
  simp only [clockTimeCode, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem randomStub_ok {a svc tr en : UInt64} {is : List Instr}
    (hg : randomStub a svc tr en = .ok is) :
    ∃ (g4 g5 g17 g18 g21 g28 : Fin 524288) (gs g30 : Fin 67108864),
      cbField (after a 4) tr = .ok g4 ∧ cbField (after a 5) (after a 24) = .ok g5 ∧
      bField (after a 15) svc = .ok gs ∧ cbField (after a 17) (after a 26) = .ok g17 ∧
      cbField (after a 18) tr = .ok g18 ∧ cbField (after a 21) (after a 11) = .ok g21 ∧
      cbField (after a 28) tr = .ok g28 ∧ bField (after a 30) en = .ok g30 ∧
      is = [.addReg 9 0 1, .ldr 10 17 0, .addImm 10 10 8, .subsReg 31 9 10, .bcond 8 g4,
          .cbz 1 g5, .orrReg 19 31 30, .addReg 20 17 0, .addImm 20 20 4095, .addImm 20 20 1,
          .orrReg 21 31 1] ++ [.orrReg 0 31 20, .orrReg 1 31 21, .movz 2 0 0, .movz 8 278 0] ++
        [.bl gs] ++ [.subsReg 31 0 21, .bcond 8 g17, .cbz 0 g18, .subReg 21 21 0,
          .addReg 20 20 0, .cbnz 21 g21, .movz 0 0 0, .ret 19, .movz 0 0 0, .ret 30] ++
        [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g28, .orrReg 0 31 12, .bl g30,
          .ret 19] := by
  unfold randomStub at hg
  cases h4 : cbField (after a 4) tr with
  | error err => simp [h4, bind, Except.bind] at hg
  | ok g4 =>
  cases h5 : cbField (after a 5) (after a 24) with
  | error err => simp [h4, h5, bind, Except.bind] at hg
  | ok g5 =>
  cases hs : bField (after a 15) svc with
  | error err => simp [h4, h5, hs, bind, Except.bind] at hg
  | ok gs =>
  cases h17 : cbField (after a 17) (after a 26) with
  | error err => simp [h4, h5, hs, h17, bind, Except.bind] at hg
  | ok g17 =>
  cases h18 : cbField (after a 18) tr with
  | error err => simp [h4, h5, hs, h17, h18, bind, Except.bind] at hg
  | ok g18 =>
  cases h21 : cbField (after a 21) (after a 11) with
  | error err => simp [h4, h5, hs, h17, h18, h21, bind, Except.bind] at hg
  | ok g21 =>
  cases ht : errorTail (after a 26) tr en with
  | error err => simp [h4, h5, hs, h17, h18, h21, ht, bind, Except.bind] at hg
  | ok tail =>
  obtain ⟨g28, g30, h28, h30, rfl⟩ := errorTail_ok ht
  simp only [h4, h5, hs, h17, h18, h21, ht, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  rw [after_after] at h28 h30
  refine ⟨g4, g5, g17, g18, g21, g28, gs, g30, rfl, rfl, rfl, rfl, rfl, rfl, h28, h30, ?_⟩
  rw [← hg]
  simp only [List.cons_append, List.nil_append]

/-! ## Steps -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- A step of `SUB Xd, Xn, #imm` with registers other than SP. -/
theorem step_subImm {s : State} {d n : Fin 32} {imm : Fin 4096} (hd : d.val < 31)
    (hn : n.val < 31) (hc : code s.pc = some (encode (.subImm d n imm))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n - UInt64.ofNat imm.val ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc (exec_subImm_x P hd hn)

/-- A step of `UDIV Xd, Xn, Xm`. -/
theorem step_udiv {s : State} {d n m : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.udiv d n m))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n / s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `STR Xt, [Xn, #(8 * i)]` to Normal memory, with a base other than SP. -/
theorem step_str {s : State} {t n : Fin 32} {i : Nat} (hi : i < 4096) (hn : n.val < 31)
    (hc : code s.pc = some (encode (.str t n ⟨i, hi⟩)))
    (hmap : ∀ k < 8, P.normal (s.x n + UInt64.ofNat (8 * i + k)) = true) :
    ∃ u, Reach P code s u ∧ u.pc = s.pc + 4 ∧ (∀ q : Fin 32, u.x q = s.x q) ∧ u.sp = s.sp ∧
      u.mem = store64 s.mem (s.x n + UInt64.ofNat (8 * i)) (s.x t) ∧ u.io = s.io :=
  ⟨_, reach_exec P code hc (exec_str_base P hi hn hmap) (.refl _), rfl, fun _ => rfl, rfl, rfl,
    rfl⟩

/-! ## The error tail -/

/-- The error tail from `a` with a result in X0: the errno of a negated error number, one whose
negation is at most 4095, returned to X19, and the trap stub `tr` for any other.  X0, X12, X30,
and the flags change. -/
theorem run_errorTail {a tr en : UInt64} {g1 : Fin 524288} {g2 : Fin 67108864}
    (hcode : CodeAt code a [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g1, .orrReg 0 31 12,
      .bl g2, .ret 19])
    (hg1 : cbField (after a 2) tr = .ok g1) (hg2 : bField (after a 4) en = .ok g2)
    (hen : CodeAt code en errnoRoutine) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 12 → q ≠ 30 → t.x q = s.x q) ∧
      if 0 - s.x 0 ≤ 4095 then t.pc = s.x 19 ∧ t.x 0 = errnoLookup errnoTable (0 - s.x 0)
      else t.pc = tr := by
  have c := fun k (hk : k < 6) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c3 := c 3 (by omega)
  have c4 := c 4 (by omega)
  have c5 := c 5 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c3 c4 c5
  have c12 : CodeAt code (after a 1) [.subsImm 31 12 4095, .bcond 8 g1] := by
    simpa using CodeAt.drop_take code hcode 1 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_subReg P code (s := s) (d := 12) (n := 31)
    (m := 0) (by decide) (by rw [hpc]; exact c0)
  have hx1 : u1.x 12 = 0 - s.x 0 := by rw [x1]; rfl
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_hiImm P code (r := 12) (imm := 4095) (tB := tr)
    (by decide) c12 (by rw [after_after]; exact cbField_target hg1) q1
  have e4095 : UInt64.ofNat (4095 : Fin 4096).val = 4095 := by decide
  rw [e4095, hx1] at p2
  by_cases hbig : 4095 < 0 - s.x 0
  · rw [ite_eq_left hbig] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1],
      fun q _ h12 _ => by rw [k2, k1 q h12], ?_⟩
    rw [ite_eq_right (UInt64.not_le.mpr hbig)]
    exact p2
  · rw [ite_eq_right hbig, after_after] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_mov P code (s := u2) (d := 0) (m := 12)
      (by decide) (by rw [p2]; exact c3)
    have q3 : u3.pc = after a 4 := by rw [p3, p2, ← after_succ]
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_bl P code (s := u3) (target := en)
      (by rw [q3]; exact c4) (by rw [q3]; exact bField_target hg2)
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_errnoRoutine P code hen p4
    have q5 : u5.pc = after a 5 := by rw [p5, x4, q3, ← after_succ]
    obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := step_ret P code (s := u5) (n := 19)
      (by rw [q5]; exact c5)
    refine ⟨u6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))),
      by rw [sp6, sp5, sp4, sp3, sp2, sp1], by rw [m6, m5, m4, m3, m2, m1],
      by rw [io6, io5, io4, io3, io2, io1],
      fun q h0 h12 h30 => by rw [k6, k5 q h0, k4 q h30, k3 q h0, k2, k1 q h12], ?_⟩
    rw [ite_eq_left (UInt64.not_lt.mp hbig)]
    refine ⟨?_, ?_⟩
    · rw [p6, k5 19 (by decide), k4 19 (by decide), k3 19 (by decide), k2, k1 19 (by decide)]
    · rw [k6, x5, k4 0 (by decide), x3, k2, hx1]

/-! ## `clock_time_get` -/

/-- The checks of `clock_time_get` from the stub's entry `a`, with the clock in X0, the time's
pointer in X2, and the area's first word at X17: the trap stub `tr` for a clock above 3 or a
pointer above that word, the return of errno 8 for a clock above 1, and otherwise
`after a 8` with the return address in X19.  X9, X19, and the flags change, and X0 on the
return. -/
theorem run_clockHead {a tr : UInt64} {g1 g4 g6 : Fin 524288}
    (hcode : CodeAt code a [.subsImm 31 0 3, .bcond 8 g1, .ldr 9 17 0, .subsReg 31 2 9,
      .bcond 8 g4, .subsImm 31 0 1, .bcond 8 g6, .orrReg 19 31 30])
    (he8 : CodeAt code (after a 46) [.movz 0 8 0, .ret 30])
    (hg1 : cbField (after a 1) tr = .ok g1) (hg4 : cbField (after a 4) tr = .ok g4)
    (hg6 : cbField (after a 6) (after a 46) = .ok g6) {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 9 → q ≠ 19 → t.x q = s.x q) ∧
      if 3 < s.x 0 ∨ load64 s.mem (s.x 17) < s.x 2 then t.pc = tr
      else if 1 < s.x 0 then t.pc = s.x 30 ∧ t.x 0 = 8
      else t.pc = after a 8 ∧ t.x 0 = s.x 0 ∧ t.x 19 = s.x 30 := by
  have c := fun k (hk : k < 8) => hcode k (by simpa using hk)
  have c2 := c 2 (by omega)
  have c7 := c 7 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c2 c7
  have c01 : CodeAt code a [.subsImm 31 0 3, .bcond 8 g1] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c34 : CodeAt code (after a 3) [.subsReg 31 2 9, .bcond 8 g4] := by
    simpa using CodeAt.drop_take code hcode 3 2 (by simp)
  have c56 : CodeAt code (after a 5) [.subsImm 31 0 1, .bcond 8 g6] := by
    simpa using CodeAt.drop_take code hcode 5 2 (by simp)
  have e0 := he8 0 (by simp)
  have e1 := he8 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at e0 e1
  have k3 : UInt64.ofNat (3 : Fin 4096).val = 3 := by decide
  have k1' : UInt64.ofNat (1 : Fin 4096).val = 1 := by decide
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiImm P code (r := 0) (imm := 3) (tB := tr)
    (by decide) c01 (cbField_target hg1) hpc
  rw [k3] at p1
  by_cases hid : 3 < s.x 0
  · rw [ite_eq_left hid] at p1
    exact ⟨u1, r1, sp1, m1, io1, fun q _ _ _ => k1 q, by rw [ite_eq_left (.inl hid)]; exact p1⟩
  rw [ite_eq_right hid] at p1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_ldr P code (s := u1) (t := 9) (n := 17)
    (i := 0) (by decide) (by decide) (by decide) (by rw [p1]; exact c2)
    (fun k hk => by rw [k1]; simpa using hmap k hk)
  have h9 : u2.x 9 = load64 s.mem (s.x 17) := by
    rw [x2, k1, m1, Nat.mul_zero, add_ofNat_zero]
  have q2 : u2.pc = after a 3 := by rw [p2, p1, ← after_succ]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_hiReg P code (x := 2) (y := 9) (tB := tr) c34
    (by rw [after_after]; exact hg4) q2
  rw [k2 2 (by decide), k1, h9] at p4
  by_cases hp : load64 s.mem (s.x 17) < s.x 2
  · rw [ite_eq_left hp] at p4
    exact ⟨u4, r1.trans (r2.trans r4), by rw [sp4, sp2, sp1], by rw [m4, m2, m1],
      by rw [io4, io2, io1], fun q _ h9 _ => by rw [k4, k2 q h9, k1],
      by rw [ite_eq_left (.inr hp)]; exact p4⟩
  rw [ite_eq_right hp, after_after] at p4
  obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := run_hiImm P code (r := 0) (imm := 1)
    (tB := after a 46) (by decide) c56 (by rw [after_after]; exact cbField_target hg6) p4
  rw [k1', k4, k2 0 (by decide), k1] at p6
  have r16 : Reach P code s u6 := r1.trans (r2.trans (r4.trans r6))
  have keep6 : ∀ q : Fin 32, q ≠ 9 → u6.x q = s.x q := fun q h9 => by
    rw [k6, k4, k2 q h9, k1]
  by_cases hid2 : 1 < s.x 0
  · rw [ite_eq_left hid2] at p6
    obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_movz P code (s := u6) (d := 0) (imm := 8)
      (hw := 0) (by decide) (by rw [p6]; exact e0)
    obtain ⟨u8, r8, p8, k8, sp8, m8, io8⟩ := step_ret P code (s := u7) (n := 30)
      (by rw [p7, p6, ← after_succ]; exact e1)
    refine ⟨u8, r16.trans (r7.trans r8), by rw [sp8, sp7, sp6, sp4, sp2, sp1],
      by rw [m8, m7, m6, m4, m2, m1], by rw [io8, io7, io6, io4, io2, io1],
      fun q h0 h9 _ => by rw [k8, k7 q h0, keep6 q h9], ?_⟩
    rw [ite_eq_right (not_or.mpr ⟨hid, hp⟩), ite_eq_left hid2]
    exact ⟨by rw [p8, k7 30 (by decide), keep6 30 (by decide)],
      by rw [k8, x7, movz0_val]; decide⟩
  · rw [ite_eq_right hid2, after_after] at p6
    obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_mov P code (s := u6) (d := 19) (m := 30)
      (by decide) (by rw [p6]; exact c7)
    refine ⟨u7, r16.trans r7, by rw [sp7, sp6, sp4, sp2, sp1], by rw [m7, m6, m4, m2, m1],
      by rw [io7, io6, io4, io2, io1], fun q _ h9 h19 => by rw [k7 q h19, keep6 q h9], ?_⟩
    rw [ite_eq_right (not_or.mpr ⟨hid, hp⟩), ite_eq_right hid2]
    exact ⟨by rw [p7, p6, ← after_succ], by rw [k7 0 (by decide), keep6 0 (by decide)],
      by rw [x7, keep6 30 (by decide)]⟩

/-- The setup of `clock_gettime` from `after a 8`: X20 at the scratch `scratch` bytes above
X17, the timespec's 16 bytes from X20 + 1040 cleared, X1 at the timespec, and X8 at 113, before
the `BL` at `after a 17`. -/
theorem run_clockCall {a : UInt64} {scratch : Nat}
    (hcode : CodeAt code (after a 8) (movImm 20 (UInt64.ofNat scratch) ++
      [.addReg 20 17 20, .str 31 20 130, .str 31 20 131, .addImm 1 20 1040, .movz 8 113 0]))
    {s : State} (hpc : s.pc = after a 8)
    (hmap : ∀ k < 16,
      P.normal (s.x 17 + UInt64.ofNat scratch + UInt64.ofNat (1040 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.pc = after a 17 ∧ t.sp = s.sp ∧ t.io = s.io ∧
      t.x 20 = s.x 17 + UInt64.ofNat scratch ∧ t.x 1 = t.x 20 + UInt64.ofNat 1040 ∧
      t.x 8 = 113 ∧ (∀ q : Fin 32, q ≠ 1 → q ≠ 8 → q ≠ 20 → t.x q = s.x q) ∧
      t.mem = store64 (store64 s.mem (t.x 20 + UInt64.ofNat 1040) 0)
        (t.x 20 + UInt64.ofNat 1048) 0 := by
  have hc := CodeAt.split code hcode (n := 4) (by simp [movImm])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movImm P code
    (d := 20) (v := UInt64.ofNat scratch) (by decide) hc.1 hpc
  have c := fun k (hk : k < 5) => hc.2 k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have c4 := c 4 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c0 c1 c2 c3 c4
  have q1 : u1.pc = after a 12 := by rw [p1, after_after]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 20) (n := 17)
    (m := 20) (by decide) (by rw [q1]; exact c0)
  have hG : u2.x 20 = s.x 17 + UInt64.ofNat scratch := by
    rw [x2, k1 17 (by decide), x1]
  have q2 : u2.pc = after a 13 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_str P code (s := u2) (t := 31) (n := 20)
    (i := 130) (by decide) (by decide) (by rw [q2]; exact c1)
    (fun k hk => by rw [hG, show 8 * 130 + k = 1040 + k by omega]; exact hmap k (by omega))
  have q3 : u3.pc = after a 14 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := step_str P code (s := u3) (t := 31) (n := 20)
    (i := 131) (by decide) (by decide) (by rw [q3]; exact c2)
    (fun k hk => by
      rw [k3, hG, show 8 * 131 + k = 1040 + (8 + k) by omega]
      exact hmap (8 + k) (by omega))
  have q4 : u4.pc = after a 15 := by rw [p4, q3, ← after_succ]
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_addImm P code (s := u4) (d := 1) (n := 20)
    (imm := 1040) (by decide) (by decide) (by rw [q4]; exact c3)
  have q5 : u5.pc = after a 16 := by rw [p5, q4, ← after_succ]
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_movz P code (s := u5) (d := 8) (imm := 113)
    (hw := 0) (by decide) (by rw [q5]; exact c4)
  have u6x20 : u6.x 20 = s.x 17 + UInt64.ofNat scratch := by
    rw [k6 20 (by decide), k5 20 (by decide), k4, k3, hG]
  refine ⟨u6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))),
    by rw [p6, q5, ← after_succ], by rw [sp6, sp5, sp4, sp3, sp2, sp1],
    by rw [io6, io5, io4, io3, io2, io1], u6x20, ?_, ?_, ?_, ?_⟩
  · rw [k6 1 (by decide), x5, k4, k3, hG, u6x20]
    rfl
  · rw [x6, movz0_val]
    rfl
  · intro q h1 h8 h20
    rw [k6 q h8, k5 q h1, k4, k3, k2 q h20, k1 q h20]
  · rw [m6, m5, m4, k3 20, k3 31, m3, hG, m2, m1, u6x20]
    rfl

/-- The handling of the result of `clock_gettime` in X0 from `after a 18`, with the scratch in
X20, the time's pointer in X2, and the return address in X19.  A result of 0 reads the seconds
and nanoseconds from the timespec at X20 + 1040: nanoseconds above `10^9 − 1` reach the trap stub
`tr`, seconds above `⌊(2^64 − 1 − nsec) / 10^9⌋` return errno 61, and any other time is stored at
the guest's pointer, X17 + 4096 + X2, with errno 0 returned.  Any other result reaches the error
tail.  X17, X18, SP, and the UART's state keep their values. -/
theorem run_clockTime {a tr en : UInt64} {g18 g26 g32 g40 : Fin 524288} {g42 : Fin 67108864}
    (hcode : CodeAt code (after a 18) (clockTimeCode g18 g26 g32 g40 g42))
    (hg18 : cbField (after a 18) (after a 40) = .ok g18) (hg26 : cbField (after a 26) tr = .ok g26)
    (hg32 : cbField (after a 32) (after a 38) = .ok g32)
    (hg40 : cbField (after a 42) tr = .ok g40) (hg42 : bField (after a 44) en = .ok g42)
    (hen : CodeAt code en errnoRoutine) {s : State} (hpc : s.pc = after a 18)
    (hmapT : ∀ k < 16, P.normal (s.x 20 + UInt64.ofNat (1040 + k)) = true)
    (hmapP : ∀ k < 8, P.normal (s.x 17 + s.x 2 + UInt64.ofNat (4096 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if s.x 0 = 0 then
        if 999999999 < load64 s.mem (s.x 20 + UInt64.ofNat 1048) then
          t.pc = tr ∧ t.mem = s.mem
        else if (0 - load64 s.mem (s.x 20 + UInt64.ofNat 1048) - 1) / 1000000000 <
            load64 s.mem (s.x 20 + UInt64.ofNat 1040) then
          t.pc = s.x 19 ∧ t.x 0 = 61 ∧ t.mem = s.mem
        else t.pc = s.x 19 ∧ t.x 0 = 0 ∧
          t.mem = store64 s.mem (s.x 17 + s.x 2 + UInt64.ofNat 4096)
            (load64 s.mem (s.x 20 + UInt64.ofNat 1048) +
              load64 s.mem (s.x 20 + UInt64.ofNat 1040) * 1000000000)
      else t.mem = s.mem ∧
        if 0 - s.x 0 ≤ 4095 then t.pc = s.x 19 ∧ t.x 0 = errnoLookup errnoTable (0 - s.x 0)
        else t.pc = tr := by
  have c := fun k (hk : k < 28) => hcode k (by simp [clockTimeCode, movImm]; omega)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c9 := c 9 (by omega)
  have c10 := c 10 (by omega)
  have c11 := c 11 (by omega)
  have c12 := c 12 (by omega)
  have c15 := c 15 (by omega)
  have c16 := c 16 (by omega)
  have c17 := c 17 (by omega)
  have c18 := c 18 (by omega)
  have c19 := c 19 (by omega)
  have c20 := c 20 (by omega)
  have c21 := c 21 (by omega)
  simp only [clockTimeCode, movImm, List.getElem_cons_zero, List.getElem_cons_succ,
    List.cons_append, List.nil_append, after_after, Nat.add_zero] at c0 c1 c2 c9 c10 c11 c12
  simp only [clockTimeCode, movImm, List.getElem_cons_zero, List.getElem_cons_succ,
    List.cons_append, List.nil_append, after_after] at c15 c16 c17 c18 c19 c20 c21
  have cmov : CodeAt code (after a 21) (movImm 11 999999999) := by
    simpa [clockTimeCode, movImm, after_after] using
      CodeAt.drop_take code hcode 3 4 (by simp [clockTimeCode, movImm])
  have c78 : CodeAt code (after a 25) [.subsReg 31 10 11, .bcond 8 g26] := by
    simpa [clockTimeCode, movImm, after_after] using
      CodeAt.drop_take code hcode 7 2 (by simp [clockTimeCode, movImm])
  have c1314 : CodeAt code (after a 31) [.subsReg 31 9 12, .bcond 8 g32] := by
    simpa [clockTimeCode, movImm, after_after] using
      CodeAt.drop_take code hcode 13 2 (by simp [clockTimeCode, movImm])
  have ctail : CodeAt code (after a 40) [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g40,
      .orrReg 0 31 12, .bl g42, .ret 19] := by
    simpa [clockTimeCode, movImm, after_after] using
      CodeAt.drop_take code hcode 22 6 (by simp [clockTimeCode, movImm])
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbnz P code (s := s) (target := after a 40)
    (by rw [hpc]; exact c0) (by rw [hpc]; exact cbField_target hg18)
  by_cases h0 : s.x 0 = 0
  swap
  · rw [ite_eq_left h0] at p1
    obtain ⟨u2, r2, sp2, m2, io2, k2, hc2⟩ := run_errorTail P code ctail
      (by rw [after_after]; exact hg40) (by rw [after_after]; exact hg42) hen p1
    rw [k1 0, k1 19] at hc2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      by rw [k2 17 (by decide) (by decide) (by decide), k1],
      by rw [k2 18 (by decide) (by decide) (by decide), k1], ?_⟩
    rw [ite_eq_right h0]
    exact ⟨by rw [m2, m1], hc2⟩
  rw [ite_eq_right (by simpa using h0), hpc, ← after_succ] at p1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_ldr P code (s := u1) (t := 9) (n := 20)
    (i := 130) (by decide) (by decide) (by decide) (by rw [p1]; exact c1)
    (fun k hk => by rw [k1, show 8 * 130 + k = 1040 + k by omega]; exact hmapT k (by omega))
  have q2 : u2.pc = after a 20 := by rw [p2, p1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_ldr P code (s := u2) (t := 10) (n := 20)
    (i := 131) (by decide) (by decide) (by decide) (by rw [q2]; exact c2)
    (fun k hk => by
      rw [k2 20 (by decide), k1, show 8 * 131 + k = 1040 + (8 + k) by omega]
      exact hmapT (8 + k) (by omega))
  have q3 : u3.pc = after a 21 := by rw [p3, q2, ← after_succ]
  generalize hsec : load64 s.mem (s.x 20 + UInt64.ofNat 1040) = sec
  generalize hnsec : load64 s.mem (s.x 20 + UInt64.ofNat 1048) = nsec
  have u3x9 : u3.x 9 = sec := by
    rw [k3 9 (by decide), x2, k1, m1, ← hsec]
  have u3x10 : u3.x 10 = nsec := by
    rw [x3, k2 20 (by decide), k1, m2, m1, ← hnsec]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_movImm P code (d := 11) (v := 999999999)
    (by decide) cmov q3
  have q4 : u4.pc = after a 25 := by rw [p4, after_after]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_hiReg P code (x := 10) (y := 11) (tB := tr) c78
    (by rw [after_after]; exact hg26) q4
  rw [x4, k4 10 (by decide), u3x10] at p5
  have r15 : Reach P code s u5 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  have keep5 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → u5.x q = s.x q := fun q h9 h10 h11 => by
    rw [k5, k4 q h11, k3 q h10, k2 q h9, k1]
  have sp5' : u5.sp = s.sp := by rw [sp5, sp4, sp3, sp2, sp1]
  have io5' : u5.io = s.io := by rw [io5, io4, io3, io2, io1]
  have m5' : u5.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  by_cases hn : 999999999 < nsec
  · rw [ite_eq_left hn] at p5
    refine ⟨u5, r15, sp5', io5', keep5 17 (by decide) (by decide) (by decide),
      keep5 18 (by decide) (by decide) (by decide), ?_⟩
    rw [ite_eq_left h0, ite_eq_left hn]
    exact ⟨p5, m5'⟩
  rw [ite_eq_right hn, after_after] at p5
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_addImm P code (s := u5) (d := 11) (n := 11)
    (imm := 1) (by decide) (by decide) (by rw [p5]; exact c9)
  have u6x11 : u6.x 11 = 1000000000 := by
    rw [x6, k5, x4]
    decide
  have q6 : u6.pc = after a 28 := by rw [p6, p5, ← after_succ]
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_subReg P code (s := u6) (d := 12) (n := 31)
    (m := 10) (by decide) (by rw [q6]; exact c10)
  have u7x12 : u7.x 12 = 0 - nsec := by
    rw [x7]
    show 0 - u6.x 10 = _
    rw [k6 10 (by decide), k5, k4 10 (by decide), u3x10]
  have q7 : u7.pc = after a 29 := by rw [p7, q6, ← after_succ]
  obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := step_subImm P code (s := u7) (d := 12) (n := 12)
    (imm := 1) (by decide) (by decide) (by rw [q7]; exact c11)
  have u8x12 : u8.x 12 = 0 - nsec - 1 := by
    rw [x8, u7x12]
    rfl
  have q8 : u8.pc = after a 30 := by rw [p8, q7, ← after_succ]
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := step_udiv P code (s := u8) (d := 12) (n := 12)
    (m := 11) (by decide) (by rw [q8]; exact c12)
  have u9x12 : u9.x 12 = (0 - nsec - 1) / 1000000000 := by
    rw [x9, u8x12, k8 11 (by decide), k7 11 (by decide), u6x11]
  have u9x9 : u9.x 9 = sec := by
    rw [k9 9 (by decide), k8 9 (by decide), k7 9 (by decide), k6 9 (by decide), k5,
      k4 9 (by decide), u3x9]
  have q9 : u9.pc = after a 31 := by rw [p9, q8, ← after_succ]
  obtain ⟨u10, r10, p10, k10, sp10, m10, io10⟩ := run_hiReg P code (x := 9) (y := 12)
    (tB := after a 38) c1314 (by rw [after_after]; exact hg32) q9
  rw [u9x12, u9x9] at p10
  have r110 : Reach P code s u10 :=
    r15.trans (r6.trans (r7.trans (r8.trans (r9.trans r10))))
  have keep10 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → u10.x q = s.x q :=
    fun q h9 h10 h11 h12 => by
      rw [k10, k9 q h12, k8 q h12, k7 q h12, k6 q h11, keep5 q h9 h10 h11]
  have sp10' : u10.sp = s.sp := by rw [sp10, sp9, sp8, sp7, sp6, sp5']
  have io10' : u10.io = s.io := by rw [io10, io9, io8, io7, io6, io5']
  have m10' : u10.mem = s.mem := by rw [m10, m9, m8, m7, m6, m5']
  by_cases hq : (0 - nsec - 1) / 1000000000 < sec
  · rw [ite_eq_left hq] at p10
    obtain ⟨u11, r11, p11, x11, k11, sp11, m11, io11⟩ := step_movz P code (s := u10) (d := 0)
      (imm := 61) (hw := 0) (by decide) (by rw [p10]; exact c20)
    obtain ⟨u12, r12, p12, k12, sp12, m12, io12⟩ := step_ret P code (s := u11) (n := 19)
      (by rw [p11, p10, ← after_succ]; exact c21)
    refine ⟨u12, r110.trans (r11.trans r12), by rw [sp12, sp11, sp10'],
      by rw [io12, io11, io10'],
      by rw [k12, k11 17 (by decide), keep10 17 (by decide) (by decide) (by decide) (by decide)],
      by rw [k12, k11 18 (by decide), keep10 18 (by decide) (by decide) (by decide) (by decide)],
      ?_⟩
    rw [ite_eq_left h0, ite_eq_right hn, ite_eq_left hq]
    refine ⟨?_, ?_, by rw [m12, m11, m10']⟩
    · rw [p12, k11 19 (by decide), keep10 19 (by decide) (by decide) (by decide) (by decide)]
    · rw [k12, x11, movz0_val]
      decide
  · rw [ite_eq_right hq, after_after] at p10
    obtain ⟨u11, r11, p11, x11, k11, sp11, m11, io11⟩ := step_madd P code (s := u10) (d := 9)
      (n := 9) (m := 11) (r := 10) (by decide) (by rw [p10]; exact c15)
    have u11x9 : u11.x 9 = nsec + sec * 1000000000 := by
      rw [x11, k10, k10, k10, u9x9, k9 10 (by decide), k8 10 (by decide), k7 10 (by decide),
        k6 10 (by decide), k5, k4 10 (by decide), u3x10, k9 11 (by decide), k8 11 (by decide),
        k7 11 (by decide), u6x11]
    have q11 : u11.pc = after a 34 := by rw [p11, p10, ← after_succ]
    obtain ⟨u12, r12, p12, x12, k12, sp12, m12, io12⟩ := step_addReg P code (s := u11) (d := 13)
      (n := 17) (m := 2) (by decide) (by rw [q11]; exact c16)
    have u12x13 : u12.x 13 = s.x 17 + s.x 2 := by
      rw [x12, k11 17 (by decide), k11 2 (by decide),
        keep10 17 (by decide) (by decide) (by decide) (by decide),
        keep10 2 (by decide) (by decide) (by decide) (by decide)]
    have q12 : u12.pc = after a 35 := by rw [p12, q11, ← after_succ]
    obtain ⟨u13, r13, p13, k13, sp13, m13, io13⟩ := step_str P code (s := u12) (t := 9) (n := 13)
      (i := 512) (by decide) (by decide) (by rw [q12]; exact c17)
      (fun k hk => by rw [u12x13, show 8 * 512 + k = 4096 + k by omega]; exact hmapP k hk)
    have q13 : u13.pc = after a 36 := by rw [p13, q12, ← after_succ]
    obtain ⟨u14, r14, p14, x14, k14, sp14, m14, io14⟩ := step_movz P code (s := u13) (d := 0)
      (imm := 0) (hw := 0) (by decide) (by rw [q13]; exact c18)
    obtain ⟨u15, r15', p15, k15, sp15, m15, io15⟩ := step_ret P code (s := u14) (n := 19)
      (by rw [p14, q13, ← after_succ]; exact c19)
    have keep13 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 →
        u13.x q = s.x q := fun q h9 h10 h11 h12 h13 => by
      rw [k13, k12 q h13, k11 q h9, keep10 q h9 h10 h11 h12]
    refine ⟨u15, r110.trans (r11.trans (r12.trans (r13.trans (r14.trans r15')))),
      by rw [sp15, sp14, sp13, sp12, sp11, sp10'], by rw [io15, io14, io13, io12, io11, io10'],
      by rw [k15, k14 17 (by decide), keep13 17 (by decide) (by decide) (by decide) (by decide)
        (by decide)],
      by rw [k15, k14 18 (by decide), keep13 18 (by decide) (by decide) (by decide) (by decide)
        (by decide)], ?_⟩
    rw [ite_eq_left h0, ite_eq_right hn, ite_eq_right hq]
    refine ⟨?_, ?_, ?_⟩
    · rw [p15, k14 19 (by decide), keep13 19 (by decide) (by decide) (by decide) (by decide)
        (by decide)]
    · rw [k15, x14, movz0_val]
      decide
    · rw [m15, m14, m13, m12, m11, m10', u12x13, k12 9 (by decide), u11x9]

/-! ## `random_get` -/

/-- The checks of `random_get` from the stub's entry `a`, with the buffer's pointer in X0, its
length in X1, and the area's first word at X17: the trap stub `tr` for a buffer that ends above
that word plus 8, the return of errno 0 for a buffer of no byte, and otherwise `after a 11` with
the return address in X19, the buffer's address X17 + X0 + 4096 in X20, and its length in X21.
X9, X10, X19 to X21, and the flags change, and X0 on the return. -/
theorem run_randomHead {a tr : UInt64} {g4 g5 : Fin 524288}
    (hcode : CodeAt code a [.addReg 9 0 1, .ldr 10 17 0, .addImm 10 10 8, .subsReg 31 9 10,
      .bcond 8 g4, .cbz 1 g5, .orrReg 19 31 30, .addReg 20 17 0, .addImm 20 20 4095,
      .addImm 20 20 1, .orrReg 21 31 1])
    (hzero : CodeAt code (after a 24) [.movz 0 0 0, .ret 30])
    (hg4 : cbField (after a 4) tr = .ok g4) (hg5 : cbField (after a 5) (after a 24) = .ok g5)
    {s : State} (hpc : s.pc = a) (hmap : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 9 → q ≠ 10 → q ≠ 19 → q ≠ 20 → q ≠ 21 → t.x q = s.x q) ∧
      if load64 s.mem (s.x 17) + 8 < s.x 0 + s.x 1 then t.pc = tr
      else if s.x 1 = 0 then t.pc = s.x 30 ∧ t.x 0 = 0
      else t.pc = after a 11 ∧ t.x 19 = s.x 30 ∧
        t.x 20 = s.x 17 + s.x 0 + UInt64.ofNat 4096 ∧ t.x 21 = s.x 1 := by
  have c := fun k (hk : k < 11) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c5 := c 5 (by omega)
  have c6 := c 6 (by omega)
  have c7 := c 7 (by omega)
  have c8 := c 8 (by omega)
  have c9 := c 9 (by omega)
  have c10 := c 10 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c5 c6
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c7 c8 c9 c10
  have c34 : CodeAt code (after a 3) [.subsReg 31 9 10, .bcond 8 g4] := by
    simpa using CodeAt.drop_take code hcode 3 2 (by simp)
  have z0 := hzero 0 (by simp)
  have z1 := hzero 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at z0 z1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 9) (n := 0)
    (m := 1) (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_ldr P code (s := u1) (t := 10) (n := 17)
    (i := 0) (by decide) (by decide) (by decide) (by rw [q1]; exact c1)
    (fun k hk => by rw [k1 17 (by decide)]; simpa using hmap k hk)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addImm P code (s := u2) (d := 10) (n := 10)
    (imm := 8) (by decide) (by decide) (by rw [q2]; exact c2)
  have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  have u3x10 : u3.x 10 = load64 s.mem (s.x 17) + 8 := by
    rw [x3, x2, k1 17 (by decide), m1, Nat.mul_zero, add_ofNat_zero]
    rfl
  have u3x9 : u3.x 9 = s.x 0 + s.x 1 := by
    rw [k3 9 (by decide), k2 9 (by decide), x1]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_hiReg P code (x := 9) (y := 10) (tB := tr) c34
    (by rw [after_after]; exact hg4) q3
  rw [u3x10, u3x9] at p4
  have keep4 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → u4.x q = s.x q := fun q h9 h10 => by
    rw [k4, k3 q h10, k2 q h10, k1 q h9]
  have r14 : Reach P code s u4 := r1.trans (r2.trans (r3.trans r4))
  have sp4' : u4.sp = s.sp := by rw [sp4, sp3, sp2, sp1]
  have io4' : u4.io = s.io := by rw [io4, io3, io2, io1]
  have m4' : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  by_cases hb : load64 s.mem (s.x 17) + 8 < s.x 0 + s.x 1
  · rw [ite_eq_left hb] at p4
    exact ⟨u4, r14, sp4', m4', io4', fun q _ h9 h10 _ _ _ => keep4 q h9 h10,
      by rw [ite_eq_left hb]; exact p4⟩
  rw [ite_eq_right hb, after_after] at p4
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbz P code (s := u4) (target := after a 24)
    (by rw [p4]; exact c5) (by rw [p4]; exact cbField_target hg5)
  rw [keep4 1 (by decide) (by decide)] at p5
  by_cases hn : s.x 1 = 0
  · rw [ite_eq_left hn] at p5
    obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_movz P code (s := u5) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [p5]; exact z0)
    obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_ret P code (s := u6) (n := 30)
      (by rw [p6, p5, ← after_succ]; exact z1)
    refine ⟨u7, r14.trans (r5.trans (r6.trans r7)), by rw [sp7, sp6, sp5, sp4'],
      by rw [m7, m6, m5, m4'], by rw [io7, io6, io5, io4'],
      fun q h0 h9 h10 _ _ _ => by rw [k7, k6 q h0, k5, keep4 q h9 h10], ?_⟩
    rw [ite_eq_right hb, ite_eq_left hn]
    exact ⟨by rw [p7, k6 30 (by decide), k5, keep4 30 (by decide) (by decide)],
      by rw [k7, x6, movz0_val]; rfl⟩
  rw [ite_eq_right hn, p4, ← after_succ] at p5
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_mov P code (s := u5) (d := 19) (m := 30)
    (by decide) (by rw [p5]; exact c6)
  have q6 : u6.pc = after a 7 := by rw [p6, p5, ← after_succ]
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_addReg P code (s := u6) (d := 20) (n := 17)
    (m := 0) (by decide) (by rw [q6]; exact c7)
  have q7 : u7.pc = after a 8 := by rw [p7, q6, ← after_succ]
  obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := step_addImm P code (s := u7) (d := 20) (n := 20)
    (imm := 4095) (by decide) (by decide) (by rw [q7]; exact c8)
  have q8 : u8.pc = after a 9 := by rw [p8, q7, ← after_succ]
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := step_addImm P code (s := u8) (d := 20) (n := 20)
    (imm := 1) (by decide) (by decide) (by rw [q8]; exact c9)
  have q9 : u9.pc = after a 10 := by rw [p9, q8, ← after_succ]
  obtain ⟨u10, r10, p10, x10, k10, sp10, m10, io10⟩ := step_mov P code (s := u9) (d := 21)
    (m := 1) (by decide) (by rw [q9]; exact c10)
  have keep9 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 19 → q ≠ 20 → u9.x q = s.x q :=
    fun q h9 h10 h19 h20 => by
      rw [k9 q h20, k8 q h20, k7 q h20, k6 q h19, k5, keep4 q h9 h10]
  refine ⟨u10, r14.trans (r5.trans (r6.trans (r7.trans (r8.trans (r9.trans r10))))),
    by rw [sp10, sp9, sp8, sp7, sp6, sp5, sp4'], by rw [m10, m9, m8, m7, m6, m5, m4'],
    by rw [io10, io9, io8, io7, io6, io5, io4'],
    fun q _ h9 h10 h19 h20 h21 => by rw [k10 q h21, keep9 q h9 h10 h19 h20], ?_⟩
  rw [ite_eq_right hb, ite_eq_right hn]
  refine ⟨by rw [p10, q9, ← after_succ], ?_, ?_, ?_⟩
  · rw [k10 19 (by decide), k9 19 (by decide), k8 19 (by decide), k7 19 (by decide), x6, k5,
      keep4 30 (by decide) (by decide)]
  · rw [k10 20 (by decide), x9, x8, x7, k6 17 (by decide), k6 0 (by decide), k5 17, k5 0,
      keep4 17 (by decide) (by decide), keep4 0 (by decide) (by decide), add_ofNat_add]
    rfl
  · rw [x10, keep9 1 (by decide) (by decide) (by decide) (by decide)]

/-- The arguments of `getrandom` from the loop's head `after a 11`: X0 at the address in X20, X1
at the count in X21, X2 at 0, and X8 at 278, before the `BL` at `after a 15`. -/
theorem run_randomCall {a : UInt64}
    (hcode : CodeAt code (after a 11) [.orrReg 0 31 20, .orrReg 1 31 21, .movz 2 0 0,
      .movz 8 278 0])
    {s : State} (hpc : s.pc = after a 11) :
    ∃ t, Reach P code s t ∧ t.pc = after a 15 ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      t.x 0 = s.x 20 ∧ t.x 1 = s.x 21 ∧ t.x 2 = 0 ∧ t.x 8 = 278 ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 8 → t.x q = s.x q) := by
  have c := fun k (hk : k < 4) => hcode k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c0 c1 c2 c3
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 0) (m := 20)
    (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 12 := by rw [p1, hpc, ← after_succ]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_mov P code (s := u1) (d := 1) (m := 21)
    (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 13 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := 2) (imm := 0)
    (hw := 0) (by decide) (by rw [q2]; exact c2)
  have q3 : u3.pc = after a 14 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_movz P code (s := u3) (d := 8) (imm := 278)
    (hw := 0) (by decide) (by rw [q3]; exact c3)
  refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), by rw [p4, q3, ← after_succ],
    by rw [sp4, sp3, sp2, sp1], by rw [m4, m3, m2, m1], by rw [io4, io3, io2, io1], ?_, ?_, ?_, ?_,
    fun q h0 h1 h2 h8 => by rw [k4 q h8, k3 q h2, k2 q h1, k1 q h0]⟩
  · rw [k4 0 (by decide), k3 0 (by decide), k2 0 (by decide), x1]
  · rw [k4 1 (by decide), k3 1 (by decide), x2, k1 21 (by decide)]
  · rw [k4 2 (by decide), x3, movz0_val]
    rfl
  · rw [x4, movz0_val]
    rfl

/-- The handling of a result of `getrandom` in X0 from `after a 16`, with the count of the bytes
that remain in X21 and their address in X20.  A result above the count reaches the error tail.
Otherwise a result of 0 reaches the trap stub `tr`, one equal to the count returns errno 0 to X19,
and any other reaches the loop's head `after a 11` with X20 advanced and X21 lowered by the
result.  X17 to X19, SP, the memory, and the UART's state keep their values. -/
theorem run_randomResult {a tr en : UInt64} {g17 g18 g21 g28 : Fin 524288}
    {g30 : Fin 67108864}
    (hcode : CodeAt code (after a 16) [.subsReg 31 0 21, .bcond 8 g17, .cbz 0 g18,
      .subReg 21 21 0, .addReg 20 20 0, .cbnz 21 g21, .movz 0 0 0, .ret 19])
    (htail : CodeAt code (after a 26) [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 g28,
      .orrReg 0 31 12, .bl g30, .ret 19])
    (hg17 : cbField (after a 17) (after a 26) = .ok g17) (hg18 : cbField (after a 18) tr = .ok g18)
    (hg21 : cbField (after a 21) (after a 11) = .ok g21) (hg28 : cbField (after a 28) tr = .ok g28)
    (hg30 : bField (after a 30) en = .ok g30) (hen : CodeAt code en errnoRoutine)
    {s : State} (hpc : s.pc = after a 16) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧ t.x 19 = s.x 19 ∧
      if s.x 21 < s.x 0 then
        if 0 - s.x 0 ≤ 4095 then t.pc = s.x 19 ∧ t.x 0 = errnoLookup errnoTable (0 - s.x 0)
        else t.pc = tr
      else if s.x 0 = 0 then t.pc = tr
      else if s.x 21 - s.x 0 = 0 then t.pc = s.x 19 ∧ t.x 0 = 0
      else t.pc = after a 11 ∧ t.x 20 = s.x 20 + s.x 0 ∧ t.x 21 = s.x 21 - s.x 0 := by
  have c := fun k (hk : k < 8) => hcode k (by simpa using hk)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have c4 := c 4 (by omega)
  have c5 := c 5 (by omega)
  have c6 := c 6 (by omega)
  have c7 := c 7 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c2 c3 c4 c5 c6 c7
  have c01 : CodeAt code (after a 16) [.subsReg 31 0 21, .bcond 8 g17] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 2 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiReg P code (x := 0) (y := 21)
    (tB := after a 26) c01 (by rw [after_after]; exact hg17) hpc
  by_cases hgt : s.x 21 < s.x 0
  · rw [ite_eq_left hgt] at p1
    obtain ⟨u2, r2, sp2, m2, io2, k2, hc2⟩ := run_errorTail P code htail
      (by rw [after_after]; exact hg28) (by rw [after_after]; exact hg30) hen p1
    rw [k1 0, k1 19] at hc2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1],
      by rw [k2 17 (by decide) (by decide) (by decide), k1],
      by rw [k2 18 (by decide) (by decide) (by decide), k1],
      by rw [k2 19 (by decide) (by decide) (by decide), k1], ?_⟩
    rw [ite_eq_left hgt]
    exact hc2
  rw [ite_eq_right hgt, after_after] at p1
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (target := tr)
    (by rw [p1]; exact c2) (by rw [p1]; exact cbField_target hg18)
  rw [k1 0] at p2
  by_cases h0 : s.x 0 = 0
  · rw [ite_eq_left h0] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1],
      by rw [k2, k1], by rw [k2, k1], by rw [k2, k1], ?_⟩
    rw [ite_eq_right hgt, ite_eq_left h0]
    exact p2
  rw [ite_eq_right h0, p1, ← after_succ] at p2
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_subReg P code (s := u2) (d := 21) (n := 21)
    (m := 0) (by decide) (by rw [p2]; exact c3)
  have q3 : u3.pc = after a 20 := by rw [p3, p2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addReg P code (s := u3) (d := 20) (n := 20)
    (m := 0) (by decide) (by rw [q3]; exact c4)
  have q4 : u4.pc = after a 21 := by rw [p4, q3, ← after_succ]
  have u4x21 : u4.x 21 = s.x 21 - s.x 0 := by
    rw [k4 21 (by decide), x3, k2, k2, k1, k1]
  have u4x20 : u4.x 20 = s.x 20 + s.x 0 := by
    rw [x4, k3 20 (by decide), k3 0 (by decide), k2, k2, k1, k1]
  have keep4 : ∀ q : Fin 32, q ≠ 20 → q ≠ 21 → u4.x q = s.x q := fun q h20 h21 => by
    rw [k4 q h20, k3 q h21, k2, k1]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbnz P code (s := u4) (target := after a 11)
    (by rw [q4]; exact c5) (by rw [q4]; exact cbField_target hg21)
  rw [u4x21] at p5
  have r15 : Reach P code s u5 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  have sp5' : u5.sp = s.sp := by rw [sp5, sp4, sp3, sp2, sp1]
  have io5' : u5.io = s.io := by rw [io5, io4, io3, io2, io1]
  have m5' : u5.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  by_cases hz : s.x 21 - s.x 0 = 0
  · rw [ite_eq_right (by simpa using hz), q4, ← after_succ] at p5
    obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_movz P code (s := u5) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [p5]; exact c6)
    obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_ret P code (s := u6) (n := 19)
      (by rw [p6, p5, ← after_succ]; exact c7)
    refine ⟨u7, r15.trans (r6.trans r7), by rw [sp7, sp6, sp5'], by rw [m7, m6, m5'],
      by rw [io7, io6, io5'],
      by rw [k7, k6 17 (by decide), k5, keep4 17 (by decide) (by decide)],
      by rw [k7, k6 18 (by decide), k5, keep4 18 (by decide) (by decide)],
      by rw [k7, k6 19 (by decide), k5, keep4 19 (by decide) (by decide)], ?_⟩
    rw [ite_eq_right hgt, ite_eq_right h0, ite_eq_left hz]
    exact ⟨by rw [p7, k6 19 (by decide), k5, keep4 19 (by decide) (by decide)],
      by rw [k7, x6, movz0_val]; rfl⟩
  · rw [ite_eq_left hz] at p5
    refine ⟨u5, r15, sp5', m5', io5', by rw [k5, keep4 17 (by decide) (by decide)],
      by rw [k5, keep4 18 (by decide) (by decide)], by rw [k5, keep4 19 (by decide) (by decide)],
      ?_⟩
    rw [ite_eq_right hgt, ite_eq_right h0, ite_eq_right hz]
    exact ⟨p5, by rw [k5, u4x20], by rw [k5, u4x21]⟩

end LeanExe.A64
