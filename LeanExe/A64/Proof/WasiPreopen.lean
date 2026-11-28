module

public import LeanExe.A64.Proof.WasiStrings
public import LeanExe.A64.Proof.StampCalls
public import LeanExe.A64.WasiPreopen

@[expose] public section

/-!
The runs of the parts of `LeanExe/A64/WasiPreopen.lean`.  In the program's model, `run_scratchAddr`
sets X20 to the scratch's address, `run_rangeCheck` reaches the trap stub when X12 exceeds the
memory's size that the area's first word gives, `run_preopenTest` passes when X0 holds 3 and the
preopen flag is nonzero, and `run_heldTest` when the descriptor in a register lies below 1,024 and
its byte is nonzero.  `run_prestatStub` and `run_dirNameStub` follow each stub from its entry to the
trap stub or to the return with its errno and its store.  In the process with the Linux call layer,
`run_preopenCheck` follows the check of descriptor 3 from its entry through the `openat` and the
`close` that its replies call for, to the return or to the exit word with status 67.
-/

namespace LeanExe.A64

open Wasm
open LeanExe.Linux (Call Replies)

/-! ## The generator's parts -/

theorem rangeCheck_ok {a tr : UInt64} {is : List Instr} (hg : rangeCheck a tr = .ok is) :
    ∃ g, cbField (after a 3) tr = .ok g ∧
      is = [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 g] := by
  unfold rangeCheck at hg
  cases h1 : cbField (after a 3) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g =>
  simp only [h1, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g, rfl, hg.symm⟩

theorem preopenTest_ok {a out : UInt64} {is : List Instr} (hg : preopenTest a out = .ok is) :
    ∃ g1 g3, cbField (after a 1) out = .ok g1 ∧ cbField (after a 3) out = .ok g3 ∧
      is = [.subsImm 31 0 3, .bcond 1 g1, .ldrb 9 20 8, .cbz 9 g3] := by
  unfold preopenTest at hg
  cases h1 : cbField (after a 1) out with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h3 : cbField (after a 3) out with
  | error err => simp [h1, h3, bind, Except.bind] at hg
  | ok g3 =>
  simp only [h1, h3, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g3, rfl, rfl, hg.symm⟩

theorem heldTest_ok {a out : UInt64} {r : Fin 32} {is : List Instr}
    (hg : heldTest a out r = .ok is) :
    ∃ g1 g4, cbField (after a 1) out = .ok g1 ∧ cbField (after a 4) out = .ok g4 ∧
      is = [.subsImm 31 r 1023, .bcond 8 g1, .addReg 10 20 r, .ldrb 9 10 16, .cbz 9 g4] := by
  unfold heldTest at hg
  cases h1 : cbField (after a 1) out with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h4 : cbField (after a 4) out with
  | error err => simp [h1, h4, bind, Except.bind] at hg
  | ok g4 =>
  simp only [h1, h4, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g4, rfl, rfl, hg.symm⟩

theorem prestatStub_ok {a tr : UInt64} {sc : Nat} {is : List Instr}
    (hg : prestatStub a tr sc = .ok is) :
    ∃ range preopen, rangeCheck (after a 1) tr = .ok range ∧
      preopenTest (after a 10) (after a 19) = .ok preopen ∧
      is = [.addImm 12 1 8] ++ range ++ scratchAddr sc ++ preopen ++
        [.addReg 10 17 1, .movz 9 1 2, .str 9 10 512, .movz 0 0 0, .ret 30, .movz 0 8 0,
          .ret 30] := by
  unfold prestatStub at hg
  cases h1 : rangeCheck (after a 1) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok range =>
  cases h2 : preopenTest (after a 10) (after a 19) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok preopen =>
  simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨range, preopen, rfl, rfl, hg.symm⟩

theorem dirNameStub_ok {a tr : UInt64} {sc : Nat} {is : List Instr}
    (hg : dirNameStub a tr sc = .ok is) :
    ∃ range preopen held g14 g24, rangeCheck (after a 1) tr = .ok range ∧
      preopenTest (after a 10) (after a 23) = .ok preopen ∧
      heldTest (after a 25) (after a 32) 0 = .ok held ∧
      cbField (after a 14) (after a 21) = .ok g14 ∧ cbField (after a 24) (after a 30) = .ok g24 ∧
      is = [.addReg 12 1 2] ++ range ++ scratchAddr sc ++ preopen ++
        [.cbz 2 g14, .addReg 10 17 1, .addImm 10 10 1, .movz 9 46 0, .strb 9 10 4095,
          .movz 0 0 0, .ret 30, .movz 0 37 0, .ret 30, .subsImm 31 0 3, .bcond 3 g24] ++ held ++
        [.movz 0 54 0, .ret 30, .movz 0 8 0, .ret 30] := by
  unfold dirNameStub at hg
  cases h1 : rangeCheck (after a 1) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok range =>
  cases h2 : preopenTest (after a 10) (after a 23) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok preopen =>
  cases h3 : heldTest (after a 25) (after a 32) 0 with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok held =>
  cases h4 : cbField (after a 14) (after a 21) with
  | error err => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok g14 =>
  cases h5 : cbField (after a 24) (after a 30) with
  | error err => simp [h1, h2, h3, h4, h5, bind, Except.bind] at hg
  | ok g24 =>
  simp only [h1, h2, h3, h4, h5, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨range, preopen, held, g14, g24, rfl, rfl, rfl, rfl, rfl, hg.symm⟩

theorem preopenCheck_ok {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) :
    ∃ b15 g18 g21 g24 g26 b28 g30 g32 b38, bField (after a 15) svc = .ok b15 ∧
      cbField (after a 18) (after a 20) = .ok g18 ∧ cbField (after a 21) (after a 23) = .ok g21 ∧
      cbField (after a 24) (after a 37) = .ok g24 ∧ cbField (after a 26) (after a 37) = .ok g26 ∧
      bField (after a 28) svc = .ok b28 ∧ cbField (after a 30) (after a 33) = .ok g30 ∧
      cbField (after a 32) (after a 37) = .ok g32 ∧ bField (after a 38) base = .ok b38 ∧
      is = [.orrReg 19 31 30] ++ scratchAddr sc ++
        [.movz 9 46 0, .strb 9 20 1080, .strb 31 20 1081, .movz 0 3 0, .addImm 1 20 1080,
          .movz 2 0x4000 0, .movk 2 8 1, .movz 3 0 0, .movz 8 56 0, .bl b15, .subReg 9 31 0,
          .subsImm 31 9 9, .bcond 1 g18, .ret 19, .subsImm 31 9 20, .bcond 1 g21, .ret 19,
          .subsImm 31 0 4, .bcond 3 g24, .lsrImm 9 0 31, .cbnz 9 g26, .movz 8 57 0, .bl b28,
          .subReg 9 31 0, .cbz 0 g30, .subsImm 31 9 4095, .bcond 8 g32, .movz 9 1 0,
          .strb 9 20 8, .strb 9 20 19, .ret 19, .movz 0 67 0, .b b38] := by
  unfold preopenCheck at hg
  cases h1 : bField (after a 15) svc with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok b15 =>
  cases h2 : cbField (after a 18) (after a 20) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g18 =>
  cases h3 : cbField (after a 21) (after a 23) with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok g21 =>
  cases h4 : cbField (after a 24) (after a 37) with
  | error err => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok g24 =>
  cases h5 : cbField (after a 26) (after a 37) with
  | error err => simp [h1, h2, h3, h4, h5, bind, Except.bind] at hg
  | ok g26 =>
  cases h6 : bField (after a 28) svc with
  | error err => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at hg
  | ok b28 =>
  cases h7 : cbField (after a 30) (after a 33) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, bind, Except.bind] at hg
  | ok g30 =>
  cases h8 : cbField (after a 32) (after a 37) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind] at hg
  | ok g32 =>
  cases h9 : bField (after a 38) base with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind] at hg
  | ok b38 =>
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  exact ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, hg.symm⟩

theorem prestatStub_length {a tr : UInt64} {sc : Nat} {is : List Instr}
    (hg : prestatStub a tr sc = .ok is) : is.length = prestatStubSize := by
  obtain ⟨range, preopen, hr, hp, rfl⟩ := prestatStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr
  obtain ⟨_, _, _, _, rfl⟩ := preopenTest_ok hp
  rfl

theorem dirNameStub_length {a tr : UInt64} {sc : Nat} {is : List Instr}
    (hg : dirNameStub a tr sc = .ok is) : is.length = dirNameStubSize := by
  obtain ⟨range, preopen, held, _, _, hr, hp, hh, _, _, rfl⟩ := dirNameStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok hr
  obtain ⟨_, _, _, _, rfl⟩ := preopenTest_ok hp
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh
  rfl

theorem preopenCheck_length {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) : is.length = preopenCheckSize := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := preopenCheck_ok hg
  rfl

/-! ## The parts' runs -/

section Runs

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- `MOVZ X0, #v` and `RET X30`: the return with `v` in X0. -/
theorem run_movzRet {a : UInt64} {v : Fin 65536} (hcode : CodeAt code a [.movz 0 v 0, .ret 30])
    {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = s.x 30 ∧ t.x 0 = UInt64.ofNat v.val ∧
      (∀ q : Fin 32, q ≠ 0 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  obtain ⟨t1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movz P code (s := s) (d := 0) (v := v)
    (by decide) (by rw [hpc]; exact c0)
  obtain ⟨t2, r2, p2, k2, sp2, m2, io2⟩ := step_ret P code (s := t1) (n := 30)
    (by rw [p1, hpc, ← after_one]; exact c1)
  exact ⟨t2, r1.trans r2, by rw [p2, k1 30 (by decide)], by rw [k2, x1],
    fun q hq => by rw [k2, k1 q hq], by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩

/-- The range check: the trap stub when X12 exceeds the memory's size, 8 plus the area's first
word, and the next word otherwise, with X13 and the flags changed. -/
theorem run_rangeCheck {a tr : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 g])
    (hg : cbField (after a 3) tr = .ok g) {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧
      (t.pc = if load64 s.mem (s.x 17) + 8 < s.x 12 then tr else after a 4) ∧
      (∀ q : Fin 32, q ≠ 13 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  have c23 : CodeAt code (after a 2) [.subsReg 31 12 13, .bcond 8 g] := by
    simpa using CodeAt.drop_take code hcode 2 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldr P code (s := s) (t := 13) (n := 17)
    (i := 0) (by decide) (by decide) (by decide) (by rw [hpc]; exact c0)
    (fun k hk => by simpa using hmap k hk)
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 13) (n := 13)
    (imm := 8) (by decide) (by decide) (by rw [p1, hpc, ← after_one]; exact c1)
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_hiReg P code c23
    (by rw [after_after]; exact hg) (s := u2)
    (by rw [p2, p1, hpc, ← after_one, ← after_one, after_after])
  refine ⟨u3, r1.trans (r2.trans r3), ?_, fun q hq => by rw [k3, k2 q hq, k1 q hq],
    by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1]⟩
  rw [p3, x2, x1, k2 12 (by decide), k1 12 (by decide), after_after]
  simp only [Nat.mul_zero, UInt64.add_zero, show UInt64.ofNat 0 = 0 from rfl,
    show UInt64.ofNat (8 : Fin 4096).val = 8 from rfl]

/-- The test of the preopened directory: the next word after it when X0 holds 3 and the preopen
flag at X20 plus 8 is nonzero, and `out` otherwise, with X9 and the flags changed. -/
theorem run_preopenTest {a out : UInt64} {g1 g3 : Fin 524288}
    (hcode : CodeAt code a [.subsImm 31 0 3, .bcond 1 g1, .ldrb 9 20 8, .cbz 9 g3])
    (hg1 : cbField (after a 1) out = .ok g1) (hg3 : cbField (after a 3) out = .ok g3)
    {s : State} (hpc : s.pc = a) (hmap : P.normal (s.x 20 + 8) = true) :
    ∃ t, Reach P code s t ∧
      (t.pc = if s.x 0 = 3 ∧ s.mem (s.x 20 + 8) ≠ 0 then after a 4 else out) ∧
      (∀ q : Fin 32, q ≠ 9 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c01 : CodeAt code a [.subsImm 31 0 3, .bcond 1 g1] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c2 c3
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_neImm P code (tB := out) (by decide) c01
    (cbField_target hg1) hpc
  rw [show UInt64.ofNat (3 : Fin 4096).val = 3 from rfl] at p1
  by_cases h3 : s.x 0 = 3
  · rw [ite_eq_left h3] at p1
    have hmap' : P.normal (u1.x 20 + UInt64.ofNat (8 : Fin 4096).val) = true := by
      rw [k1]
      exact hmap
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_setX P code (s := u1) (d := 9)
      (by decide) (by rw [p1]; exact c2) (exec_ldrb_base P (t := 9) (by decide) hmap')
    obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_cbz P code (s := u2) (target := out)
      (by rw [p2, p1, ← after_succ]; exact c3)
      (by rw [p2, p1, ← after_succ]; exact cbField_target hg3)
    refine ⟨u3, r1.trans (r2.trans r3), ?_, fun q hq => by rw [k3, k2 q hq, k1],
      by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1]⟩
    rw [p3, x2, m1, k1, p2, p1, ← after_succ, ← after_succ]
    simp only [show UInt64.ofNat (8 : Fin 4096).val = 8 from rfl, h3, true_and]
    by_cases hb : s.mem (s.x 20 + 8) = 0
    · rw [ite_eq_left (by rw [hb]; rfl), ite_eq_right (by simp [hb])]
    · rw [ite_eq_right (by
        intro h
        apply hb
        have := congrArg UInt64.toNat h
        simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat] at this
        exact UInt8.toNat_inj.mp this), ite_eq_left hb]
  · rw [ite_eq_right h3] at p1
    exact ⟨u1, r1, by rw [p1, ite_eq_right (fun h => h3 h.1)], fun q _ => k1 q, sp1, m1, io1⟩

/-- The test whether the shim holds the descriptor in X`r`: the next word after it when the
descriptor lies at most 1,023 and its byte at X20 plus 16 is nonzero, and `out` otherwise, with X9,
X10, and the flags changed. -/
theorem run_heldTest {a out : UInt64} {r : Fin 32} {g1 g4 : Fin 524288} (hr : r.val < 31)
    (hcode : CodeAt code a
      [.subsImm 31 r 1023, .bcond 8 g1, .addReg 10 20 r, .ldrb 9 10 16, .cbz 9 g4])
    (hg1 : cbField (after a 1) out = .ok g1) (hg4 : cbField (after a 4) out = .ok g4)
    {s : State} (hpc : s.pc = a)
    (hmap : s.x r ≤ 1023 → P.normal (s.x 20 + s.x r + 16) = true) :
    ∃ t, Reach P code s t ∧
      (t.pc = if s.x r ≤ 1023 ∧ s.mem (s.x 20 + s.x r + 16) ≠ 0 then after a 5 else out) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  have c01 : CodeAt code a [.subsImm 31 r 1023, .bcond 8 g1] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  have c4 := hcode 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c2 c3 c4
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiImm P code (tB := out) hr c01
    (cbField_target hg1) hpc
  rw [show UInt64.ofNat (1023 : Fin 4096).val = 1023 from rfl] at p1
  by_cases hlo : s.x r ≤ 1023
  · rw [ite_eq_right (UInt64.not_lt.mpr hlo)] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 10) (n := 20)
      (m := r) (by decide) (by rw [p1]; exact c2)
    have hmap' : P.normal (u2.x 10 + UInt64.ofNat (16 : Fin 4096).val) = true := by
      rw [x2, k1, k1]
      exact hmap hlo
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_setX P code (s := u2) (d := 9)
      (by decide) (by rw [p2, p1, ← after_succ]; exact c3)
      (exec_ldrb_base P (t := 9) (by decide) hmap')
    obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := step_cbz P code (s := u3) (target := out)
      (by rw [p3, p2, p1, ← after_succ, ← after_succ]; exact c4)
      (by rw [p3, p2, p1, ← after_succ, ← after_succ]; exact cbField_target hg4)
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), ?_,
      fun q h9 h10 => by rw [k4, k3 q h9, k2 q h10, k1], by rw [sp4, sp3, sp2, sp1],
      by rw [m4, m3, m2, m1], by rw [io4, io3, io2, io1]⟩
    rw [p4, x3, m2, m1, x2, k1, k1, p3, p2, p1, ← after_succ, ← after_succ, ← after_succ]
    simp only [show UInt64.ofNat (16 : Fin 4096).val = 16 from rfl, hlo, true_and]
    by_cases hb : s.mem (s.x 20 + s.x r + 16) = 0
    · rw [ite_eq_left (by rw [hb]; rfl), ite_eq_right (by simp [hb])]
    · rw [ite_eq_right (by
        intro h
        apply hb
        have := congrArg UInt64.toNat h
        simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat] at this
        exact UInt8.toNat_inj.mp this), ite_eq_left hb]
  · rw [ite_eq_left (UInt64.not_le.mp hlo)] at p1
    exact ⟨u1, r1, by rw [p1, ite_eq_right (fun h => hlo h.1)], fun q _ _ => k1 q, sp1, m1, io1⟩

/-- A step of `STRB` with a base other than SP to the byte `addr` of Normal memory, other than the
UART's. -/
theorem step_strbAt {s : State} {t n : Fin 32} {imm : Fin 4096} {k : Nat} {addr : UInt64}
    (hn : n.val < 31) (hc : code s.pc = some (encode (.strb t n imm))) (hk : imm.val = k)
    (haddr : s.x n + UInt64.ofNat k = addr) (hmap : P.normal addr = true) (hne : addr ≠ P.uart) :
    ∃ s', Reach P code s s' ∧ s'.pc = s.pc + 4 ∧ (∀ q : Fin 32, s'.x q = s.x q) ∧
      s'.sp = s.sp ∧ s'.io = s.io ∧ s'.mem = store8 s.mem addr (s.x t).toUInt8 := by
  subst hk haddr
  have h31 : (n.val != 31) = true := by simp; omega
  have he : LeanExe.A64.exec P (.strb t n imm) s = some { s with
      mem := store8 s.mem (s.x n + UInt64.ofNat imm.val) (s.x t).toUInt8, pc := s.pc + 4 } := by
    simp only [exec, State.xsp_eq_x hn, State.spAligned, h31, Bool.true_or, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hne, hmap]
  exact ⟨_, reach_exec P code hc he (.refl _), rfl, fun _ => rfl, rfl, rfl, rfl⟩

theorem byte_ne_zero {b : UInt8} : b.toUInt64 ≠ 0 ↔ b ≠ 0 := by
  constructor
  · intro h hb
    exact h (by rw [hb]; rfl)
  · intro h hb
    apply h
    have := congrArg UInt64.toNat hb
    simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat] at this
    exact UInt8.toNat_inj.mp this

/-- The stub of `fd_prestat_get` from its entry: the trap stub when the record's 8 bytes from the
guest address in X1 exceed the memory, and otherwise the return to X30, with errno 0 and the word
`2^32` stored at the guest address for descriptor 3 while the preopen flag is nonzero, and with
errno 8 and the memory kept for every other descriptor and for descriptor 3 while the flag is
zero. -/
theorem run_prestatStub {a tr : UInt64} {sc : Nat} {is : List Instr}
    (hg : prestatStub a tr sc = .ok is) (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a)
    (hsize : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true)
    (hflag : P.normal (s.x 17 + UInt64.ofNat sc + 8) = true)
    (hrec : ¬ load64 s.mem (s.x 17) + 8 < s.x 1 + 8 →
      ∀ k < 8, P.normal (s.x 17 + s.x 1 + UInt64.ofNat (8 * 512 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if load64 s.mem (s.x 17) + 8 < s.x 1 + 8 then t.pc = tr
      else t.pc = s.x 30 ∧
        if s.x 0 = 3 ∧ s.mem (s.x 17 + UInt64.ofNat sc + 8) ≠ 0 then
          t.x 0 = 0 ∧ t.mem = store64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat (8 * 512)) (2 ^ 32)
        else t.x 0 = 8 ∧ t.mem = s.mem := by
  obtain ⟨range, preopen, hr, hp, rfl⟩ := prestatStub_ok hg
  obtain ⟨g4, hg4, rfl⟩ := rangeCheck_ok hr
  obtain ⟨g11, g13, hg11, hg13, rfl⟩ := preopenTest_ok hp
  have cA := CodeAt.split code hcode (n := 14) (by simp [scratchAddr, movImm])
  have cB := CodeAt.split code cA.1 (n := 10) (by simp [scratchAddr, movImm])
  have cC := CodeAt.split code cB.1 (n := 5) (by simp)
  have cD := CodeAt.split code cC.1 (n := 1) (by simp)
  have c0 := (CodeAt.cons.mp cD.1).1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addImm P code (s := s) (d := 12) (n := 1)
    (imm := 8) (by decide) (by decide) (by rw [hpc]; exact c0)
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_rangeCheck P code cD.2
    hg4 (s := u1) (by rw [p1, hpc, ← after_one])
    (fun k hk => by rw [k1 17 (by decide)]; exact hsize k hk)
  rw [m1, k1 17 (by decide), x1, show UInt64.ofNat (8 : Fin 4096).val = 8 from rfl,
    after_after] at p2
  have k12 : ∀ q : Fin 32, q ≠ 12 → q ≠ 13 → u2.x q = s.x q := fun q h12 h13 => by
    rw [k2 q h13, k1 q h12]
  by_cases htr : load64 s.mem (s.x 17) + 8 < s.x 1 + 8
  · rw [ite_eq_left htr] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1], k12 17 (by decide) (by decide),
      k12 18 (by decide) (by decide), ?_⟩
    rw [ite_eq_left htr]
    exact p2
  rw [ite_eq_right htr] at p2
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_scratchAddr P code cC.2 (s := u2) p2
  have h16 : u3.x 20 = s.x 17 + UInt64.ofNat sc := by rw [x3, k12 17 (by decide) (by decide)]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_preopenTest P code cB.2
    hg11 hg13 (s := u3)
    (by rw [p3, after_after]) (by rw [h16]; exact hflag)
  have k0 : u3.x 0 = s.x 0 := by rw [k3 0 (by decide), k12 0 (by decide) (by decide)]
  rw [h16, m3, m2, m1, k0, after_after] at p4
  have kk : ∀ q : Fin 32, q ≠ 9 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u4.x q = s.x q :=
    fun q h9 h12 h13 h16 => by rw [k4 q h9, k3 q h16, k12 q h12 h13]
  have hm4 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  have r14 : Reach P code s u4 := r1.trans (r2.trans (r3.trans r4))
  by_cases hgr : s.x 0 = 3 ∧ s.mem (s.x 17 + UInt64.ofNat sc + 8) ≠ 0
  · rw [ite_eq_left hgr] at p4
    have t0 := cA.2 0 (by simp)
    have t1 := cA.2 1 (by simp)
    have t2 := cA.2 2 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at t0 t1 t2
    have t34 : CodeAt code (after a 17) [.movz 0 0 0, .ret 30] := by
      simpa [after_after] using CodeAt.drop_take code cA.2 3 2 (by simp)
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_addReg P code (s := u4) (d := 10)
      (n := 17) (m := 1) (by decide) (by rw [p4]; exact t0)
    obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_movz P code (s := u5) (d := 9) (imm := 1)
      (hw := 2) (by decide) (by rw [p5, p4, ← after_succ]; exact t1)
    have hx10 : u6.x 10 = s.x 17 + s.x 1 := by
      rw [k6 10 (by decide), x5, kk 17 (by decide) (by decide) (by decide) (by decide),
        kk 1 (by decide) (by decide) (by decide) (by decide)]
    have hex := exec_str_base P (s := u6) (t := 9) (n := 10) (i := 512) (by decide) (by decide)
      (fun k hk => by rw [hx10]; exact hrec htr k hk)
    let u7 : State :=
      { u6 with
        mem := store64 u6.mem (u6.x 10 + UInt64.ofNat (8 * 512)) (u6.x 9)
        pc := u6.pc + 4 }
    have r7 : Reach P code u6 u7 :=
      reach_exec P code (by rw [p6, p5, p4, ← after_succ, ← after_succ]; exact t2) hex (.refl _)
    obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := run_movzRet P code t34 (s := u7)
      (by show u6.pc + 4 = _; rw [p6, p5, p4, ← after_succ, ← after_succ, ← after_succ])
    have kk6 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u6.x q = s.x q :=
      fun q h9 h10 h12 h13 h16 => by rw [k6 q h9, k5 q h10, kk q h9 h12 h13 h16]
    refine ⟨u8, r14.trans (r5.trans (r6.trans (r7.trans r8))), ?_, ?_, ?_, ?_, ?_⟩
    · rw [sp8]
      show u6.sp = _
      rw [sp6, sp5, sp4, sp3, sp2, sp1]
    · rw [io8]
      show u6.io = _
      rw [io6, io5, io4, io3, io2, io1]
    · rw [k8 17 (by decide)]
      exact kk6 17 (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [k8 18 (by decide)]
      exact kk6 18 (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [ite_eq_right htr, ite_eq_left hgr]
      refine ⟨?_, by rw [x8]; rfl, ?_⟩
      · rw [p8]
        exact kk6 30 (by decide) (by decide) (by decide) (by decide) (by decide)
      · rw [m8]
        show store64 u6.mem (u6.x 10 + UInt64.ofNat (8 * 512)) (u6.x 9) = _
        rw [hx10, x6, m6, m5, hm4]
        rfl
  · rw [ite_eq_right hgr] at p4
    have t56 : CodeAt code (after a 19) [.movz 0 8 0, .ret 30] := by
      simpa [after_after] using CodeAt.drop_take code cA.2 5 2 (by simp)
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_movzRet P code t56 (s := u4) p4
    refine ⟨u5, r14.trans r5, by rw [sp5, sp4, sp3, sp2, sp1], by rw [io5, io4, io3, io2, io1],
      by rw [k5 17 (by decide)]; exact kk 17 (by decide) (by decide) (by decide) (by decide),
      by rw [k5 18 (by decide)]; exact kk 18 (by decide) (by decide) (by decide) (by decide), ?_⟩
    rw [ite_eq_right htr, ite_eq_right hgr]
    exact ⟨by rw [p5]; exact kk 30 (by decide) (by decide) (by decide) (by decide),
      by rw [x5]; rfl, by rw [m5, hm4]⟩

/-- The stub of `fd_prestat_dir_name` from its entry: the trap stub when the buffer of X2 bytes
from the guest address in X1 exceeds the memory, and otherwise the return to X30.  For descriptor
3 while the preopen flag is nonzero it returns errno 37 for an empty buffer and otherwise errno 0
with `.` stored at the buffer.  For every other descriptor, and for descriptor 3 while the flag is
zero, it returns errno 54 for a descriptor below 3 and for one of at most 1,023 whose byte is
nonzero, and errno 8 otherwise, with the memory kept. -/
theorem run_dirNameStub {a tr : UInt64} {sc : Nat} {is : List Instr}
    (hg : dirNameStub a tr sc = .ok is) (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a)
    (hsize : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true)
    (hflag : P.normal (s.x 17 + UInt64.ofNat sc + 8) = true)
    (hheld : s.x 0 ≤ 1023 → P.normal (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) = true)
    (hbuf : ¬ load64 s.mem (s.x 17) + 8 < s.x 1 + s.x 2 → s.x 2 ≠ 0 →
      P.normal (s.x 17 + s.x 1 + 1 + 4095) = true)
    (hbufU : ¬ load64 s.mem (s.x 17) + 8 < s.x 1 + s.x 2 → s.x 2 ≠ 0 →
      s.x 17 + s.x 1 + 1 + 4095 ≠ P.uart) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if load64 s.mem (s.x 17) + 8 < s.x 1 + s.x 2 then t.pc = tr
      else t.pc = s.x 30 ∧
        if s.x 0 = 3 ∧ s.mem (s.x 17 + UInt64.ofNat sc + 8) ≠ 0 then
          if s.x 2 = 0 then t.x 0 = 37 ∧ t.mem = s.mem
          else t.x 0 = 0 ∧ t.mem = store8 s.mem (s.x 17 + s.x 1 + 1 + 4095) 46
        else if s.x 0 < 3 ∨
            (s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0) then
          t.x 0 = 54 ∧ t.mem = s.mem
        else t.x 0 = 8 ∧ t.mem = s.mem := by
  obtain ⟨range, preopen, held, g14, g24, hr, hp, hh, hg14, hg24, rfl⟩ := dirNameStub_ok hg
  obtain ⟨g4, hg4, rfl⟩ := rangeCheck_ok hr
  obtain ⟨g11, g13, hg11, hg13, rfl⟩ := preopenTest_ok hp
  obtain ⟨g26, g29, hg26, hg29, rfl⟩ := heldTest_ok hh
  have cA := CodeAt.split code hcode (n := 30) (by simp [scratchAddr, movImm])
  have cB := CodeAt.split code cA.1 (n := 25) (by simp [scratchAddr, movImm])
  have cC := CodeAt.split code cB.1 (n := 14) (by simp [scratchAddr, movImm])
  have cD := CodeAt.split code cC.1 (n := 10) (by simp [scratchAddr, movImm])
  have cE := CodeAt.split code cD.1 (n := 5) (by simp)
  have cF := CodeAt.split code cE.1 (n := 1) (by simp)
  have c0 := (CodeAt.cons.mp cF.1).1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 12) (n := 1)
    (m := 2) (by decide) (by rw [hpc]; exact c0)
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_rangeCheck P code cF.2
    hg4 (s := u1) (by rw [p1, hpc, ← after_one])
    (fun k hk => by rw [k1 17 (by decide)]; exact hsize k hk)
  rw [m1, k1 17 (by decide), x1, after_after] at p2
  have k12 : ∀ q : Fin 32, q ≠ 12 → q ≠ 13 → u2.x q = s.x q := fun q h12 h13 => by
    rw [k2 q h13, k1 q h12]
  by_cases htr : load64 s.mem (s.x 17) + 8 < s.x 1 + s.x 2
  · rw [ite_eq_left htr] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1], k12 17 (by decide) (by decide),
      k12 18 (by decide) (by decide), ?_⟩
    rw [ite_eq_left htr]
    exact p2
  rw [ite_eq_right htr] at p2
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_scratchAddr P code cE.2 (s := u2) p2
  have h16 : u3.x 20 = s.x 17 + UInt64.ofNat sc := by rw [x3, k12 17 (by decide) (by decide)]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_preopenTest P code cD.2
    hg11 hg13 (s := u3)
    (by rw [p3, after_after]) (by rw [h16]; exact hflag)
  have k0 : u3.x 0 = s.x 0 := by rw [k3 0 (by decide), k12 0 (by decide) (by decide)]
  rw [h16, m3, m2, m1, k0, after_after] at p4
  have kk : ∀ q : Fin 32, q ≠ 9 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u4.x q = s.x q :=
    fun q h9 h12 h13 h16 => by rw [k4 q h9, k3 q h16, k12 q h12 h13]
  have hm4 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  have hsp4 : u4.sp = s.sp := by rw [sp4, sp3, sp2, sp1]
  have hio4 : u4.io = s.io := by rw [io4, io3, io2, io1]
  have r14 : Reach P code s u4 := r1.trans (r2.trans (r3.trans r4))
  -- the return with an errno from `after a b`, two words `MOVZ X0` and `RET`
  have ret : ∀ {b : Nat} {v : Fin 65536} {u : State},
      CodeAt code (after a b) [.movz 0 v 0, .ret 30] → u.pc = after a b → Reach P code s u →
      u.sp = s.sp → u.io = s.io → u.mem = s.mem →
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u.x q = s.x q) →
      ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧
        t.x 18 = s.x 18 ∧ t.pc = s.x 30 ∧ t.x 0 = UInt64.ofNat v.val ∧ t.mem = s.mem := by
    intro b v u hc hu ru hsp hio hm hk
    obtain ⟨t, rt, pt, xt, kt, spt, mt, iot⟩ := run_movzRet P code hc (s := u) hu
    have h17 : t.x 17 = s.x 17 := by
      rw [kt 17 (by decide)]
      exact hk 17 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h18 : t.x 18 = s.x 18 := by
      rw [kt 18 (by decide)]
      exact hk 18 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h30 : t.pc = s.x 30 := by
      rw [pt]
      exact hk 30 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨t, ru.trans rt, by rw [spt, hsp], by rw [iot, hio], h17, h18, h30, xt,
      by rw [mt, hm]⟩
  have kk4 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u4.x q = s.x q :=
    fun q h9 _ h12 h13 h16 => kk q h9 h12 h13 h16
  by_cases hgr : s.x 0 = 3 ∧ s.mem (s.x 17 + UInt64.ofNat sc + 8) ≠ 0
  · rw [ite_eq_left hgr] at p4
    have t0 := (CodeAt.cons.mp cC.2).1
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbz P code (s := u4) (target := after a 21)
      (by rw [p4]; exact t0) (by rw [p4]; exact cbField_target hg14)
    rw [kk 2 (by decide) (by decide) (by decide) (by decide), p4] at p5
    have kk5 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u5.x q = s.x q :=
      fun q h9 h10 h12 h13 h16 => by rw [k5 q, kk4 q h9 h10 h12 h13 h16]
    by_cases h2 : s.x 2 = 0
    · rw [ite_eq_left h2] at p5
      have t78 : CodeAt code (after a 21) [.movz 0 37 0, .ret 30] := by
        simpa [after_after] using CodeAt.drop_take code cC.2 7 2 (by simp)
      obtain ⟨t, rt, spt, iot, x17, x18, pt, xt, mt⟩ := ret t78 p5 (r14.trans r5)
        (by rw [sp5, hsp4]) (by rw [io5, hio4]) (by rw [m5, hm4]) kk5
      refine ⟨t, rt, spt, iot, x17, x18, ?_⟩
      rw [ite_eq_right htr, ite_eq_left hgr, ite_eq_left h2]
      exact ⟨pt, by rw [xt]; rfl, mt⟩
    · rw [ite_eq_right h2, ← after_succ] at p5
      have t1 := cC.2 1 (by simp)
      have t2 := cC.2 2 (by simp)
      have t3 := cC.2 3 (by simp)
      have t4 := cC.2 4 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at t1 t2 t3 t4
      have t56 : CodeAt code (after a 19) [.movz 0 0 0, .ret 30] := by
        simpa [after_after] using CodeAt.drop_take code cC.2 5 2 (by simp)
      obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_addReg P code (s := u5) (d := 10)
        (n := 17) (m := 1) (by decide) (by rw [p5]; exact t1)
      obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_addImm P code (s := u6) (d := 10)
        (n := 10) (imm := 1) (by decide) (by decide) (by rw [p6, p5, ← after_succ]; exact t2)
      obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := run_movz P code (s := u7) (d := 9) (v := 46)
        (by decide) (by rw [p7, p6, p5, ← after_succ, ← after_succ]; exact t3)
      have hx10 : u8.x 10 = s.x 17 + s.x 1 + 1 := by
        rw [k8 10 (by decide), x7, x6, kk5 17 (by decide) (by decide) (by decide) (by decide)
          (by decide), kk5 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl
      obtain ⟨u9, r9, p9, k9, sp9, io9, m9⟩ := step_strbAt P code (s := u8) (t := 9) (n := 10)
        (imm := 4095) (k := 4095) (addr := s.x 17 + s.x 1 + 1 + 4095) (by decide)
        (by rw [p8, p7, p6, p5, ← after_succ, ← after_succ, ← after_succ]; exact t4) rfl
        (by rw [hx10]; rfl) (hbuf htr h2) (hbufU htr h2)
      have kk9 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u9.x q = s.x q :=
        fun q h9 h10 h12 h13 h16 => by
          rw [k9 q, k8 q h9, k7 q h10, k6 q h10, kk5 q h9 h10 h12 h13 h16]
      obtain ⟨u10, r10, p10, x10, k10, sp10, m10, io10⟩ := run_movzRet P code t56 (s := u9)
        (by rw [p9, p8, p7, p6, p5, ← after_succ, ← after_succ, ← after_succ, ← after_succ])
      have h17 : u10.x 17 = s.x 17 := by
        rw [k10 17 (by decide)]
        exact kk9 17 (by decide) (by decide) (by decide) (by decide) (by decide)
      have h18 : u10.x 18 = s.x 18 := by
        rw [k10 18 (by decide)]
        exact kk9 18 (by decide) (by decide) (by decide) (by decide) (by decide)
      refine ⟨u10, r14.trans (r5.trans (r6.trans (r7.trans (r8.trans (r9.trans r10))))),
        by rw [sp10, sp9, sp8, sp7, sp6, sp5, hsp4], by rw [io10, io9, io8, io7, io6, io5, hio4],
        h17, h18, ?_⟩
      rw [ite_eq_right htr, ite_eq_left hgr, ite_eq_right h2]
      have h30 : u10.pc = s.x 30 := by
        rw [p10]
        exact kk9 30 (by decide) (by decide) (by decide) (by decide) (by decide)
      refine ⟨h30, by rw [x10]; rfl, ?_⟩
      rw [m10, m9, x8, m8, m7, m6, m5, hm4]
      rfl
  · rw [ite_eq_right hgr] at p4
    have kk4 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u4.x q = s.x q :=
      fun q h9 _ h12 h13 h16 => kk q h9 h12 h13 h16
    have c23 : CodeAt code (after a 23) [.subsImm 31 0 3, .bcond 3 g24] := by
      simpa [after_after] using CodeAt.drop_take code cC.2 9 2 (by simp)
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_loImm P code (tB := after a 30) (by decide) c23
      (by rw [after_after]; exact cbField_target hg24) p4
    rw [show UInt64.ofNat (3 : Fin 4096).val = 3 from rfl,
      kk 0 (by decide) (by decide) (by decide) (by decide), after_after] at p5
    have kk5 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u5.x q = s.x q :=
      fun q h9 h10 h12 h13 h16 => by rw [k5 q, kk4 q h9 h10 h12 h13 h16]
    have t30 : CodeAt code (after a 30) [.movz 0 54 0, .ret 30] := by
      simpa [after_after] using CodeAt.drop_take code cA.2 0 2 (by simp)
    have t32 : CodeAt code (after a 32) [.movz 0 8 0, .ret 30] := by
      simpa [after_after] using CodeAt.drop_take code cA.2 2 2 (by simp)
    by_cases hlo : s.x 0 < 3
    · rw [ite_eq_left hlo] at p5
      obtain ⟨t, rt, spt, iot, x17, x18, pt, xt, mt⟩ := ret t30 p5 (r14.trans r5)
        (by rw [sp5, hsp4]) (by rw [io5, hio4]) (by rw [m5, hm4]) kk5
      refine ⟨t, rt, spt, iot, x17, x18, ?_⟩
      rw [ite_eq_right htr, ite_eq_right hgr, ite_eq_left (Or.inl hlo)]
      exact ⟨pt, by rw [xt]; rfl, mt⟩
    · rw [ite_eq_right hlo] at p5
      have h16' : u5.x 20 = s.x 17 + UInt64.ofNat sc := by rw [k5, k4 20 (by decide), h16]
      have h0' : u5.x 0 = s.x 0 := kk5 0 (by decide) (by decide) (by decide) (by decide)
        (by decide)
      obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := run_heldTest P code (r := 0) (by decide) cB.2
        hg26 hg29 (s := u5) p5
        (by rw [h16', h0']; exact hheld)
      rw [h16', h0', m5, hm4, after_after] at p6
      have kk6 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u6.x q = s.x q :=
        fun q h9 h10 h12 h13 h16 => by rw [k6 q h9 h10, kk5 q h9 h10 h12 h13 h16]
      have hm6 : u6.mem = s.mem := by rw [m6, m5, hm4]
      by_cases hh : s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0
      · rw [ite_eq_left hh] at p6
        obtain ⟨t, rt, spt, iot, x17, x18, pt, xt, mt⟩ := ret t30 p6 (r14.trans (r5.trans r6))
          (by rw [sp6, sp5, hsp4]) (by rw [io6, io5, hio4]) hm6 kk6
        refine ⟨t, rt, spt, iot, x17, x18, ?_⟩
        rw [ite_eq_right htr, ite_eq_right hgr, ite_eq_left (Or.inr hh)]
        exact ⟨pt, by rw [xt]; rfl, mt⟩
      · rw [ite_eq_right hh] at p6
        obtain ⟨t, rt, spt, iot, x17, x18, pt, xt, mt⟩ := ret t32 p6 (r14.trans (r5.trans r6))
          (by rw [sp6, sp5, hsp4]) (by rw [io6, io5, hio4]) hm6 kk6
        refine ⟨t, rt, spt, iot, x17, x18, ?_⟩
        rw [ite_eq_right htr, ite_eq_right hgr, ite_eq_right (fun h => h.elim hlo hh)]
        exact ⟨pt, by rw [xt]; rfl, mt⟩

end Runs

/-! ## The check of descriptor 3 -/

/-- The event of the startup's `openat` of `.` at `path` under descriptor 3 with arm64's flags
`O_RDONLY | O_DIRECTORY | O_CLOEXEC`, whose reply is `r`. -/
def preopenOpenEvent (path : UInt64) (r : LeanExe.Linux.Reply) : LeanExe.Linux.Event :=
  ⟨LeanExe.Linux.openatCall, [3, path, 0x84000, 0], [[46, 0]], [], r.ret, []⟩

/-- The event of the startup's `close` of the descriptor `d`, whose reply is `r`. -/
def preopenCloseEvent (d : UInt64) (r : LeanExe.Linux.Reply) : LeanExe.Linux.Event :=
  ⟨LeanExe.Linux.closeCall, [d], [], [], r.ret, []⟩

/-- The layer events of the check of descriptor 3 with the path at `path` and the replies `R` from
call `k` on, and its outcome: `some false` after `-EBADF` or `-ENOTDIR`, `some true` after a
descriptor from 4 to `2^31 - 1` whose `close` returns 0 or a negated error number, and `none`, the
end with status 67, after every other result. -/
def preopenRun (path : UInt64) (R : Replies) (k : Nat) :
    List LeanExe.Linux.Event × Option Bool :=
  if (R k).ret = 0 - 9 ∨ (R k).ret = 0 - 20 then ([preopenOpenEvent path (R k)], some false)
  else if 4 ≤ (R k).ret.toNat ∧ (R k).ret.toNat < 2 ^ 31 then
    if (R (k + 1)).ret = 0 ∨ LeanExe.Linux.isError (R (k + 1)).ret = true then
      ([preopenOpenEvent path (R k), preopenCloseEvent (R k).ret (R (k + 1))], some true)
    else ([preopenOpenEvent path (R k), preopenCloseEvent (R k).ret (R (k + 1))], none)
  else ([preopenOpenEvent path (R k)], none)

/-- The layer events and the outcome of the startup routine of an executable with the scratch `G`
and the replies `R`: those of `preopenRun` for the path buffer when `check` holds, and no event
and no grant otherwise. -/
def startup (check : Bool) (G : Scratch) (R : Replies) : List LeanExe.Linux.Event × Option Bool :=
  if check then preopenRun G.path R 0 else ([], some false)

/-- The memory after the check of descriptor 3 with the scratch at `G`: `.` and its terminating
zero at the path buffer, and after a grant the preopen flag and the byte of descriptor 3 at 1. -/
def preopenMem (m : UInt64 → UInt8) (G : UInt64) (granted : Bool) : UInt64 → UInt8 :=
  if granted then store8 (store8 (store8 (store8 m (G + 1080) 46) (G + 1081) 0) (G + 8) 1) (G + 19) 1
  else store8 (store8 m (G + 1080) 46) (G + 1081) 0

theorem neg_eq_ofNat {r : UInt64} {k : Nat} :
    0 - r = UInt64.ofNat k ↔ r = 0 - UInt64.ofNat k := by
  constructor <;> intro h <;> apply UInt64.toNat_inj.mp <;>
    have := congrArg UInt64.toNat h <;>
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow] at * <;>
    have := r.toNat_lt <;> simp only [Nat.reducePow] at * <;> omega

theorem shiftRight31_eq_zero (r : UInt64) :
    r >>> UInt64.ofNat 31 = 0 ↔ r.toNat < 2 ^ 31 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
  simp only [Nat.reducePow, Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt64.reduceToNat]
  omega

theorem isError_neg {c : UInt64} (h0 : c ≠ 0) :
    LeanExe.Linux.isError c = true ↔ ¬ UInt64.ofNat 4095 < 0 - c := by
  have hc : c.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by rw [h]; rfl))
  simp only [LeanExe.Linux.isError, decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_sub,
    UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow, Nat.reduceMod]
  have := c.toNat_lt
  simp only [Nat.reducePow] at *
  omega

section Check

variable {T : List Call} {R : Replies} {P : Platform} {code : UInt64 → Option UInt32}

/-- The code of the check of descriptor 3 at `a`, from its generator: the move of X30, the
scratch's address, and the words after them. -/
theorem preopenCheck_code {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) (hcode : CodeAt code a is) :
    ∃ b15 g18 g21 g24 g26 b28 g30 g32 b38, bField (after a 15) svc = .ok b15 ∧
      cbField (after a 18) (after a 20) = .ok g18 ∧ cbField (after a 21) (after a 23) = .ok g21 ∧
      cbField (after a 24) (after a 37) = .ok g24 ∧ cbField (after a 26) (after a 37) = .ok g26 ∧
      bField (after a 28) svc = .ok b28 ∧ cbField (after a 30) (after a 33) = .ok g30 ∧
      cbField (after a 32) (after a 37) = .ok g32 ∧ bField (after a 38) base = .ok b38 ∧
      code a = some (encode (.orrReg 19 31 30)) ∧ CodeAt code (after a 1) (scratchAddr sc) ∧
      CodeAt code (after a 6)
        [.movz 9 46 0, .strb 9 20 1080, .strb 31 20 1081, .movz 0 3 0, .addImm 1 20 1080,
          .movz 2 0x4000 0, .movk 2 8 1, .movz 3 0 0, .movz 8 56 0, .bl b15, .subReg 9 31 0,
          .subsImm 31 9 9, .bcond 1 g18, .ret 19, .subsImm 31 9 20, .bcond 1 g21, .ret 19,
          .subsImm 31 0 4, .bcond 3 g24, .lsrImm 9 0 31, .cbnz 9 g26, .movz 8 57 0, .bl b28,
          .subReg 9 31 0, .cbz 0 g30, .subsImm 31 9 4095, .bcond 8 g32, .movz 9 1 0,
          .strb 9 20 8, .strb 9 20 19, .ret 19, .movz 0 67 0, .b b38] := by
  obtain ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, h15, h18, h21, h24, h26, h28, h30, h32,
    h38, rfl⟩ := preopenCheck_ok hg
  have cs := CodeAt.split code hcode (n := 6) (by simp [scratchAddr, movImm])
  have cs1 := CodeAt.split code cs.1 (n := 1) rfl
  exact ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, h15, h18, h21, h24, h26, h28, h30, h32,
    h38, (CodeAt.cons.mp cs1.1).1, cs1.2, cs.2⟩

theorem exec_movk (P : Platform) (s : State) (d : Fin 32) (imm : Fin 65536) (hw : Fin 4) :
    LeanExe.A64.exec P (.movk d imm hw) s =
      some { s.setX d
            ((s.x d &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * hw.val))) |||
              UInt64.ofNat imm.val <<< UInt64.ofNat (16 * hw.val))
          with pc := s.pc + 4 } := rfl

/-- The words of the check of descriptor 3 from its entry to its `BL` of `openat`: X19 at X30, X20
at the scratch's address `G`, `.` and its terminating zero at the path buffer, and the arguments
of `openat` in X0 to X3 with its number 56 in X8. -/
theorem run_preopenFront {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = a) (hU : P.normal P.uart = false)
    (hpath : ∀ j < 2, P.normal (s.x 17 + UInt64.ofNat sc + UInt64.ofNat (1080 + j)) = true) :
    ∃ t, Reach P code s t ∧ t.pc = after a 15 ∧ t.x 0 = 3 ∧
      t.x 1 = s.x 17 + UInt64.ofNat sc + 1080 ∧ t.x 2 = 0x84000 ∧ t.x 3 = 0 ∧ t.x 8 = 56 ∧
      t.x 20 = s.x 17 + UInt64.ofNat sc ∧ t.x 19 = s.x 30 ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      t.x 30 = s.x 30 ∧ t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = store8 (store8 s.mem (s.x 17 + UInt64.ofNat sc + 1080) 46)
        (s.x 17 + UInt64.ofNat sc + 1081) 0 := by
  obtain ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, -, -, -, -, -, -, -, -, -, c0, cS, cT⟩ :=
    preopenCheck_code hg hcode
  have c6 := cT 0 (by simp)
  have c7 := cT 1 (by simp)
  have c8 := cT 2 (by simp)
  have c9 := cT 3 (by simp)
  have c10 := cT 4 (by simp)
  have c11 := cT 5 (by simp)
  have c12 := cT 6 (by simp)
  have c13 := cT 7 (by simp)
  have c14 := cT 8 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c6 c7 c8 c9 c10
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c11 c12 c13 c14
  obtain ⟨u0, r0, p0, x0, k0, sp0, m0, io0⟩ := step_mov P code (s := s) (d := 19) (m := 30)
    (by decide) (by rw [hpc]; exact c0)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_scratchAddr P code cS (s := u0)
    (by rw [p0, hpc, ← after_one])
  rw [after_after] at p1
  have hG : u1.x 20 = s.x 17 + UInt64.ofNat sc := by rw [x1, k0 17 (by decide)]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movz P code (s := u1) (d := 9) (v := 46)
    (by decide) (by rw [p1]; exact c6)
  obtain ⟨u3, r3, p3, k3, sp3, io3, m3⟩ := step_strb P code (s := u2) (t := 9) (n := 20)
    (imm := 1080) (k := 1080) (addr := s.x 17 + UInt64.ofNat sc + 1080) (by decide)
    (by rw [p2, p1, ← after_succ]; exact c7) rfl
    (by rw [k2 20 (by decide), hG]; rfl) (by simpa using hpath 0 (by decide)) hU
  obtain ⟨u4, r4, p4, k4, sp4, io4, m4⟩ := step_strb P code (s := u3) (t := 31) (n := 20)
    (imm := 1081) (k := 1081) (addr := s.x 17 + UInt64.ofNat sc + 1081) (by decide)
    (by rw [p3, p2, p1, ← after_succ, ← after_succ]; exact c8) rfl
    (by rw [k3, k2 20 (by decide), hG]; rfl)
    (by simpa using hpath 1 (by decide)) hU
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_movz P code (s := u4) (d := 0) (v := 3)
    (by decide) (by rw [p4, p3, p2, p1, ← after_succ, ← after_succ, ← after_succ]; exact c9)
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_addImm P code (s := u5) (d := 1) (n := 20)
    (imm := 1080) (by decide) (by decide)
    (by
      rw [p5, p4, p3, p2, p1, ← after_succ, ← after_succ, ← after_succ, ← after_succ]
      exact c10)
  have p6' : u6.pc = after a 11 := by
    rw [p6, p5, p4, p3, p2, p1, ← after_succ, ← after_succ, ← after_succ, ← after_succ,
      ← after_succ]
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := run_movz P code (s := u6) (d := 2) (v := 0x4000)
    (by decide) (by rw [p6']; exact c11)
  have e8 : LeanExe.A64.exec P (.movk 2 8 1) u7 =
      some { u7.setX 2 0x84000 with pc := u7.pc + 4 } := by
    rw [exec_movk, x7]
    rfl
  obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := step_setX P code (s := u7) (d := 2) (by decide)
    (by rw [p7, p6', ← after_succ]; exact c12) e8
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := run_movz P code (s := u8) (d := 3) (v := 0)
    (by decide) (by rw [p8, p7, p6', ← after_succ, ← after_succ]; exact c13)
  obtain ⟨u10, r10, p10, x10, k10, sp10, m10, io10⟩ := run_movz P code (s := u9) (d := 8)
    (v := 56) (by decide)
    (by rw [p9, p8, p7, p6', ← after_succ, ← after_succ, ← after_succ]; exact c14)
  have kk : ∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 3 → q ≠ 8 → q ≠ 9 → q ≠ 20 → q ≠ 19 →
      u10.x q = s.x q := fun q h0 h1 h2 h3 h8 h9 h16 h19 => by
    rw [k10 q h8, k9 q h3, k8 q h2, k7 q h2, k6 q h1, k5 q h0, k4, k3, k2 q h9, k1 q h16,
      k0 q h19]
  refine ⟨u10, r0.trans (r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans
    (r7.trans (r8.trans (r9.trans r10))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    kk 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    kk 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    kk 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    by rw [sp10, sp9, sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1, sp0],
    by rw [io10, io9, io8, io7, io6, io5, io4, io3, io2, io1, io0], ?_⟩
  · rw [p10, p9, p8, p7, p6', ← after_succ, ← after_succ, ← after_succ, ← after_succ]
  · rw [k10 0 (by decide), k9 0 (by decide), k8 0 (by decide), k7 0 (by decide),
      k6 0 (by decide), x5]
    rfl
  · rw [k10 1 (by decide), k9 1 (by decide), k8 1 (by decide), k7 1 (by decide), x6,
      k5 20 (by decide), k4, k3, k2 20 (by decide), hG]
    rfl
  · rw [k10 2 (by decide), k9 2 (by decide), x8]
  · rw [k10 3 (by decide), x9]
    rfl
  · rw [x10]
    rfl
  · rw [k10 20 (by decide), k9 20 (by decide), k8 20 (by decide), k7 20 (by decide),
      k6 20 (by decide), k5 20 (by decide), k4, k3, k2 20 (by decide), hG]
  · rw [k10 19 (by decide), k9 19 (by decide), k8 19 (by decide), k7 19 (by decide),
      k6 19 (by decide), k5 19 (by decide), k4, k3, k2 19 (by decide), k1 19 (by decide), x0]
  · rw [m10, m9, m8, m7, m6, m5, m4, m3, k3, x2, m2, m1, m0]
    rfl

/-- The words of the check of descriptor 3 after the `openat`, from `after a 16` with its result
in X0: a return to X19 after `-EBADF` or `-ENOTDIR`; the `BL` of `close` at `after a 28` with 57
in X8 after a descriptor from 4 to `2^31 - 1`; and the exit's words at `after a 37` after every
other result.  X8, X9, and the flags change. -/
theorem run_preopenOpened {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 16) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.mem = s.mem ∧
      (∀ q : Fin 32, q ≠ 8 → q ≠ 9 → t.x q = s.x q) ∧
      if s.x 0 = 0 - 9 ∨ s.x 0 = 0 - 20 then t.pc = s.x 19
      else if 4 ≤ (s.x 0).toNat ∧ (s.x 0).toNat < 2 ^ 31 then t.pc = after a 28 ∧ t.x 8 = 57
      else t.pc = after a 37 := by
  obtain ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, -, h18, h21, h24, h26, -, -, -, -, -, -,
    cT⟩ := preopenCheck_code hg hcode
  have c16 := cT 10 (by simp)
  have c19 := cT 13 (by simp)
  have c22 := cT 16 (by simp)
  have c25 := cT 19 (by simp)
  have c26 := cT 20 (by simp)
  have c27 := cT 21 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c16 c19 c22 c25
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c26 c27
  have c17 : CodeAt code (after a 17) [.subsImm 31 9 9, .bcond 1 g18] := by
    simpa [after_after] using CodeAt.drop_take code cT 11 2 (by simp)
  have c20 : CodeAt code (after a 20) [.subsImm 31 9 20, .bcond 1 g21] := by
    simpa [after_after] using CodeAt.drop_take code cT 14 2 (by simp)
  have c23 : CodeAt code (after a 23) [.subsImm 31 0 4, .bcond 3 g24] := by
    simpa [after_after] using CodeAt.drop_take code cT 17 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_subReg P code (s := s) (d := 9) (n := 31)
    (m := 0) (by decide) (by rw [hpc]; exact c16)
  have hx9 : u1.x 9 = 0 - s.x 0 := x1
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_neImm P code (tB := after a 20) (r := 9)
    (by decide) c17 (by rw [after_after]; exact cbField_target h18) (s := u1)
    (by rw [p1, hpc, ← after_succ])
  rw [hx9, show UInt64.ofNat (9 : Fin 4096).val = UInt64.ofNat 9 from rfl, after_after] at p2
  have kk2 : ∀ q : Fin 32, q ≠ 9 → u2.x q = s.x q := fun q h9 => by rw [k2, k1 q h9]
  have ret19 : ∀ {b : Nat} {u : State}, code (after a b) = some (encode (.ret 19)) →
      u.pc = after a b → Reach P code s u → u.sp = s.sp → u.io = s.io → u.mem = s.mem →
      (∀ q : Fin 32, q ≠ 9 → u.x q = s.x q) →
      ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.mem = s.mem ∧
        (∀ q : Fin 32, q ≠ 8 → q ≠ 9 → t.x q = s.x q) ∧ t.pc = s.x 19 := by
    intro b u hc hu ru hsp hio hm hk
    obtain ⟨t, rt, pt, kt, spt, mt, iot⟩ := step_ret P code (s := u) (n := 19)
      (by rw [hu]; exact hc)
    exact ⟨t, ru.trans rt, by rw [spt, hsp], by rw [iot, hio], by rw [mt, hm],
      fun q _ h9 => by rw [kt, hk q h9], by rw [pt, hk 19 (by decide)]⟩
  by_cases hb : s.x 0 = 0 - 9
  · rw [ite_eq_left (neg_eq_ofNat.mpr hb)] at p2
    obtain ⟨t, rt, spt, iot, mt, kt, pt⟩ := ret19 c19 p2 (r1.trans r2) (by rw [sp2, sp1])
      (by rw [io2, io1]) (by rw [m2, m1]) kk2
    exact ⟨t, rt, spt, iot, mt, kt, by rw [ite_eq_left (Or.inl hb)]; exact pt⟩
  rw [ite_eq_right (fun h => hb (neg_eq_ofNat.mp h))] at p2
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_neImm P code (tB := after a 23) (r := 9)
    (by decide) c20 (by rw [after_after]; exact cbField_target h21) (s := u2) p2
  rw [k2, hx9, show UInt64.ofNat (20 : Fin 4096).val = UInt64.ofNat 20 from rfl,
    after_after] at p3
  have kk3 : ∀ q : Fin 32, q ≠ 9 → u3.x q = s.x q := fun q h9 => by rw [k3, kk2 q h9]
  by_cases he : s.x 0 = 0 - 20
  · rw [ite_eq_left (neg_eq_ofNat.mpr he)] at p3
    obtain ⟨t, rt, spt, iot, mt, kt, pt⟩ := ret19 c22 p3 (r1.trans (r2.trans r3))
      (by rw [sp3, sp2, sp1]) (by rw [io3, io2, io1]) (by rw [m3, m2, m1]) kk3
    exact ⟨t, rt, spt, iot, mt, kt, by rw [ite_eq_left (Or.inr he)]; exact pt⟩
  rw [ite_eq_right (fun h => he (neg_eq_ofNat.mp h))] at p3
  have hnot : ¬ (s.x 0 = 0 - 9 ∨ s.x 0 = 0 - 20) := fun h => h.elim hb he
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_loImm P code (tB := after a 37) (r := 0)
    (by decide) c23 (by rw [after_after]; exact cbField_target h24) (s := u3) p3
  rw [kk3 0 (by decide), after_after] at p4
  have r14 : Reach P code s u4 := r1.trans (r2.trans (r3.trans r4))
  have kk4 : ∀ q : Fin 32, q ≠ 9 → u4.x q = s.x q := fun q h9 => by rw [k4, kk3 q h9]
  by_cases hlo : s.x 0 < UInt64.ofNat (4 : Fin 4096).val
  · rw [ite_eq_left hlo] at p4
    have hlo' : ¬ 4 ≤ (s.x 0).toNat := by
      rw [UInt64.lt_iff_toNat_lt] at hlo
      have e4 : (UInt64.ofNat (4 : Fin 4096).val).toNat = 4 := rfl
      omega
    refine ⟨u4, r14, by rw [sp4, sp3, sp2, sp1], by rw [io4, io3, io2, io1],
      by rw [m4, m3, m2, m1], fun q _ h9 => kk4 q h9, ?_⟩
    rw [ite_eq_right hnot, ite_eq_right (fun h => hlo' h.1)]
    exact p4
  rw [ite_eq_right hlo] at p4
  have hhi : 4 ≤ (s.x 0).toNat := by
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le] at hlo
    have e4 : (UInt64.ofNat (4 : Fin 4096).val).toNat = 4 := rfl
    omega
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_lsrImm P code (s := u4) (d := 9) (n := 0)
    (sh := 31) (k := 31) (by decide) (by rw [p4]; exact c25) rfl
  obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := step_cbnz P code (s := u5) (target := after a 37)
    (by rw [p5, p4, ← after_succ]; exact c26)
    (by rw [p5, p4, ← after_succ]; exact cbField_target h26)
  rw [x5, kk4 0 (by decide), p5, p4, ← after_succ, ← after_succ] at p6
  have kk6 : ∀ q : Fin 32, q ≠ 9 → u6.x q = s.x q := fun q h9 => by rw [k6, k5 q h9, kk4 q h9]
  by_cases hbig : s.x 0 >>> UInt64.ofNat 31 ≠ 0
  · rw [ite_eq_left hbig] at p6
    have hbig' : ¬ (s.x 0).toNat < 2 ^ 31 := fun h => hbig ((shiftRight31_eq_zero _).mpr h)
    refine ⟨u6, r14.trans (r5.trans r6), by rw [sp6, sp5, sp4, sp3, sp2, sp1],
      by rw [io6, io5, io4, io3, io2, io1], by rw [m6, m5, m4, m3, m2, m1],
      fun q _ h9 => kk6 q h9, ?_⟩
    rw [ite_eq_right hnot, ite_eq_right (fun h => hbig' h.2)]
    exact p6
  rw [ite_eq_right hbig] at p6
  have hsmall : (s.x 0).toNat < 2 ^ 31 := (shiftRight31_eq_zero _).mp (not_not.mp hbig)
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := run_movz P code (s := u6) (d := 8) (v := 57)
    (by decide) (by rw [p6]; exact c27)
  refine ⟨u7, r14.trans (r5.trans (r6.trans r7)), by rw [sp7, sp6, sp5, sp4, sp3, sp2, sp1],
    by rw [io7, io6, io5, io4, io3, io2, io1], by rw [m7, m6, m5, m4, m3, m2, m1],
    fun q h8 h9 => by rw [k7 q h8, kk6 q h9], ?_⟩
  rw [ite_eq_right hnot, ite_eq_left ⟨hhi, hsmall⟩]
  exact ⟨by rw [p7, p6, ← after_succ], by rw [x7]; rfl⟩

/-- The words of the check of descriptor 3 after the `close`, from `after a 29` with its result in
X0 and the scratch's address in X20: after 0 or a negated error number, the preopen flag and the
byte of descriptor 3 set to 1 and a return to X19, and the exit's words at `after a 37`
otherwise.  X9 and the flags change. -/
theorem run_preopenClosed {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 29) (hU : P.normal P.uart = false)
    (hflag : P.normal (s.x 20 + 8) = true) (hheld : P.normal (s.x 20 + 19) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 9 → t.x q = s.x q) ∧
      if s.x 0 = 0 ∨ LeanExe.Linux.isError (s.x 0) = true then
        t.pc = s.x 19 ∧ t.mem = store8 (store8 s.mem (s.x 20 + 8) 1) (s.x 20 + 19) 1
      else t.pc = after a 37 ∧ t.mem = s.mem := by
  obtain ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, -, -, -, -, -, -, h30, h32, -, -, -,
    cT⟩ := preopenCheck_code hg hcode
  have c29 := cT 23 (by simp)
  have c30 := cT 24 (by simp)
  have c33 := cT 27 (by simp)
  have c34 := cT 28 (by simp)
  have c35 := cT 29 (by simp)
  have c36 := cT 30 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c29 c30 c33 c34
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c35 c36
  have c31 : CodeAt code (after a 31) [.subsImm 31 9 4095, .bcond 8 g32] := by
    simpa [after_after] using CodeAt.drop_take code cT 25 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_subReg P code (s := s) (d := 9) (n := 31)
    (m := 0) (by decide) (by rw [hpc]; exact c29)
  have hx9 : u1.x 9 = 0 - s.x 0 := x1
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (target := after a 33)
    (by rw [p1, hpc, ← after_succ]; exact c30)
    (by rw [p1, hpc, ← after_succ]; exact cbField_target h30)
  rw [k1 0 (by decide), p1, hpc, ← after_succ, ← after_succ] at p2
  have kk2 : ∀ q : Fin 32, q ≠ 9 → u2.x q = s.x q := fun q h9 => by rw [k2, k1 q h9]
  have grant : ∀ {u : State}, u.pc = after a 33 → Reach P code s u → u.sp = s.sp →
      u.io = s.io → u.mem = s.mem → (∀ q : Fin 32, q ≠ 9 → u.x q = s.x q) →
      ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧
        (∀ q : Fin 32, q ≠ 9 → t.x q = s.x q) ∧ t.pc = s.x 19 ∧
        t.mem = store8 (store8 s.mem (s.x 20 + 8) 1) (s.x 20 + 19) 1 := by
    intro u hu ru hsp hio hm hk
    obtain ⟨v1, rv1, pv1, xv1, kv1, spv1, mv1, iov1⟩ := run_movz P code (s := u) (d := 9)
      (v := 1) (by decide) (by rw [hu]; exact c33)
    obtain ⟨v2, rv2, pv2, kv2, spv2, iov2, mv2⟩ := step_strb P code (s := v1) (t := 9) (n := 20)
      (imm := 8) (k := 8) (addr := s.x 20 + 8) (by decide)
      (by rw [pv1, hu, ← after_succ]; exact c34) rfl
      (by rw [kv1 20 (by decide), hk 20 (by decide)]; rfl) hflag hU
    obtain ⟨v3, rv3, pv3, kv3, spv3, iov3, mv3⟩ := step_strb P code (s := v2) (t := 9) (n := 20)
      (imm := 19) (k := 19) (addr := s.x 20 + 19) (by decide)
      (by rw [pv2, pv1, hu, ← after_succ, ← after_succ]; exact c35) rfl
      (by rw [kv2, kv1 20 (by decide), hk 20 (by decide)]; rfl) hheld hU
    obtain ⟨v4, rv4, pv4, kv4, spv4, mv4, iov4⟩ := step_ret P code (s := v3) (n := 19)
      (by rw [pv3, pv2, pv1, hu, ← after_succ, ← after_succ, ← after_succ]; exact c36)
    refine ⟨v4, ru.trans (rv1.trans (rv2.trans (rv3.trans rv4))),
      by rw [spv4, spv3, spv2, spv1, hsp], by rw [iov4, iov3, iov2, iov1, hio],
      fun q h9 => by rw [kv4, kv3, kv2, kv1 q h9, hk q h9],
      by rw [pv4, kv3, kv2, kv1 19 (by decide), hk 19 (by decide)], ?_⟩
    rw [mv4, mv3, mv2, kv2, xv1, mv1, hm]
    rfl
  by_cases h0 : s.x 0 = 0
  · rw [ite_eq_left h0] at p2
    obtain ⟨t, rt, spt, iot, kt, pt, mt⟩ := grant p2 (r1.trans r2) (by rw [sp2, sp1])
      (by rw [io2, io1]) (by rw [m2, m1]) kk2
    exact ⟨t, rt, spt, iot, kt, by rw [ite_eq_left (Or.inl h0)]; exact ⟨pt, mt⟩⟩
  rw [ite_eq_right h0] at p2
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_hiImm P code (tB := after a 37) (r := 9)
    (by decide) c31 (by rw [after_after]; exact cbField_target h32) (s := u2) p2
  rw [k2, hx9, show UInt64.ofNat (4095 : Fin 4096).val = UInt64.ofNat 4095 from rfl,
    after_after] at p3
  have kk3 : ∀ q : Fin 32, q ≠ 9 → u3.x q = s.x q := fun q h9 => by rw [k3, kk2 q h9]
  by_cases herr : UInt64.ofNat 4095 < 0 - s.x 0
  · rw [ite_eq_left herr] at p3
    have hne : ¬ (s.x 0 = 0 ∨ LeanExe.Linux.isError (s.x 0) = true) := fun h =>
      h.elim h0 fun he => (isError_neg h0).mp he herr
    exact ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1], kk3,
      by rw [ite_eq_right hne]; exact ⟨p3, by rw [m3, m2, m1]⟩⟩
  rw [ite_eq_right herr] at p3
  obtain ⟨t, rt, spt, iot, kt, pt, mt⟩ := grant p3 (r1.trans (r2.trans r3))
    (by rw [sp3, sp2, sp1]) (by rw [io3, io2, io1]) (by rw [m3, m2, m1]) kk3
  exact ⟨t, rt, spt, iot, kt,
    by rw [ite_eq_left (Or.inr ((isError_neg h0).mpr herr))]; exact ⟨pt, mt⟩⟩

/-- The exit's words of the check of descriptor 3, from `after a 37`: status 67 in X0 and the
exit word `base`. -/
theorem run_preopenExit {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 37) :
    ∃ t, Reach P code s t ∧ t.pc = base ∧ t.x 0 = 67 ∧ t.io = s.io := by
  obtain ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, -, -, -, -, -, -, -, -, h38, -, -,
    cT⟩ := preopenCheck_code hg hcode
  have c37 := cT 31 (by simp)
  have c38 := cT 32 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c37 c38
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movz P code (s := s) (d := 0) (v := 67)
    (by decide) (by rw [hpc]; exact c37)
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_b P code (s := u1) (target := base)
    (by rw [p1, hpc, ← after_succ]; exact c38)
    (by rw [p1, hpc, ← after_succ]; exact bField_target h38)
  exact ⟨u2, r1.trans r2, p2, by rw [k2, x1]; rfl, by rw [io2, io1]⟩


theorem add_ofNat_ne (G : UInt64) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    G + UInt64.ofNat i ≠ G + UInt64.ofNat j := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
  have := G.toNat_lt
  simp only [Nat.reducePow] at *
  omega

/-- The bytes that the check of descriptor 3 writes at the path buffer: `.` and its terminating
zero. -/
theorem preopenPath_bytes (m : UInt64 → UInt8) (G : UInt64) :
    (store8 (store8 m (G + 1080) 46) (G + 1081) 0) (G + 1080) = 46 ∧
      (store8 (store8 m (G + 1080) 46) (G + 1081) 0) (G + 1081) = 0 := by
  have ne : G + 1080 ≠ G + 1081 := add_ofNat_ne G (i := 1080) (j := 1081) (by decide) (by decide)
    (by decide)
  refine ⟨?_, ?_⟩
  · show (if G + 1080 = G + 1081 then 0 else if G + 1080 = G + 1080 then 46 else m (G + 1080)) = 46
    rw [ite_eq_right ne, ite_eq_left rfl]
  · show (if G + 1081 = G + 1081 then (0 : UInt8) else _) = 0
    rw [ite_eq_left rfl]

/-- `preopenMem` keeps every byte but the path buffer's first two, the preopen flag, and the byte
of descriptor 3. -/
theorem preopenMem_other (m : UInt64 → UInt8) (G : UInt64) (granted : Bool) {b : UInt64}
    (h1 : b ≠ G + 1080) (h2 : b ≠ G + 1081) (h3 : b ≠ G + 8) (h4 : b ≠ G + 19) :
    preopenMem m G granted b = m b := by
  cases granted <;> simp [preopenMem, store8, h1, h2, h3, h4]

/-- The preopen flag after the check of descriptor 3: 1 after a grant, and its byte otherwise. -/
theorem preopenMem_flag (m : UInt64 → UInt8) (G : UInt64) (granted : Bool) :
    preopenMem m G granted (G + 8) = if granted then 1 else m (G + 8) := by
  have n19 : G + 8 ≠ G + 19 := add_ofNat_ne G (i := 8) (j := 19) (by decide) (by decide) (by decide)
  have n80 : G + 8 ≠ G + 1080 :=
    add_ofNat_ne G (i := 8) (j := 1080) (by decide) (by decide) (by decide)
  have n81 : G + 8 ≠ G + 1081 :=
    add_ofNat_ne G (i := 8) (j := 1081) (by decide) (by decide) (by decide)
  cases granted <;> simp [preopenMem, store8, n19, n80, n81]

/-- The byte of descriptor 3 after the check of descriptor 3: 1 after a grant, and its byte
otherwise. -/
theorem preopenMem_held3 (m : UInt64 → UInt8) (G : UInt64) (granted : Bool) :
    preopenMem m G granted (G + 19) = if granted then 1 else m (G + 19) := by
  have n80 : G + 19 ≠ G + 1080 :=
    add_ofNat_ne G (i := 19) (j := 1080) (by decide) (by decide) (by decide)
  have n81 : G + 19 ≠ G + 1081 :=
    add_ofNat_ne G (i := 19) (j := 1081) (by decide) (by decide) (by decide)
  cases granted <;> simp [preopenMem, store8, n80, n81]

/-- The check of descriptor 3 from its entry in the process with the Linux call layer, for the
replies `R` from call `p.trace.length` on: the layer events and the outcome of `preopenRun` for the
path buffer at the scratch's address `G` plus 1,080.  After a grant or no grant the process returns
to X30 with SP, X17, and X18 kept and the memory of `preopenMem`, and otherwise it stands at the
exit word with status 67.  `FPCR` and the UART's state keep their values. -/
theorem run_preopenCheck {a svc base : UInt64} {sc : Nat} {is : List Instr}
    (hg : preopenCheck a svc base sc = .ok is) (hcode : CodeAt code a is)
    (hsvc : OpsAt code svc [.svc, .ins (.ret 30)])
    (hT56 : T.find? (fun c => c.arm64 == 56) = some LeanExe.Linux.openatCall)
    (hT57 : T.find? (fun c => c.arm64 == 57) = some LeanExe.Linux.closeCall)
    (hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55) (hbase : base.toNat < 2 ^ 55)
    (hU : P.normal P.uart = false) {p : Proc} (hpc : p.core.pc = a) (hfp : p.fpcr = fpcrValue)
    (hret : (p.core.x 30).toNat < 2 ^ 55) {G : UInt64} (hGx : p.core.x 17 + UInt64.ofNat sc = G)
    {k : Nat} (hk : p.trace.length = k)
    (hpath : ∀ j < 2, P.normal (G + UInt64.ofNat (1080 + j)) = true)
    (hflag : P.normal (G + 8) = true) (hheld : P.normal (G + 19) = true) :
    ∃ q, ProcReachWith T R P code p q ∧ q.fpcr = fpcrValue ∧ q.core.io = p.core.io ∧
      q.trace = p.trace ++ (preopenRun (G + 1080) R k).1.map Event.sys ∧
      match (preopenRun (G + 1080) R k).2 with
      | some granted => q.core.pc = p.core.x 30 ∧ q.core.sp = p.core.sp ∧
          q.core.x 17 = p.core.x 17 ∧ q.core.x 18 = p.core.x 18 ∧
          q.core.mem = preopenMem p.core.mem G granted
      | none => q.core.pc = base ∧ q.core.x 0 = 67 := by
  subst hGx hk
  obtain ⟨u, ru, pu, x0u, x1u, x2u, x3u, x8u, x16u, x19u, x17u, x18u, -, spu, iou, mu⟩ :=
    run_preopenFront (P := P) hg hcode (s := p.core) hpc hU hpath
  obtain ⟨b15, g18, g21, g24, g26, b28, g30, g32, b38, h15, -, -, -, -, h28, -, -, -, -, -,
    cT⟩ := preopenCheck_code hg hcode
  have c15 := cT 9 (by simp)
  have c16 := cT 10 (by simp)
  have c28 := cT 22 (by simp)
  have c29 := cT 23 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c15 c16 c28 c29
  have q1 : ProcReachWith T R P code p { p with core := u } :=
    ProcReachWith.of_reach' hdom hfp ru (by rw [pu]; exact hdom _ _ c15)
  generalize hG : p.core.x 17 + UInt64.ofNat sc = G at *
  -- the `openat`
  have hpb := preopenPath_bytes p.core.mem G
  have h1081 : G + 1080 + 1 = G + 1081 := by rw [UInt64.add_assoc]; rfl
  have hz : (a64Memory P).read u.mem (u.x 1 + UInt64.ofNat 1) = 0 := by
    show u.mem (u.x 1 + UInt64.ofNat 1) = 0
    rw [mu, x1u, show UInt64.ofNat 1 = 1 from rfl, h1081]
    exact hpb.2
  have hnz : ∀ i < 1, (a64Memory P).read u.mem (u.x 1 + UInt64.ofNat i) ≠ 0 := by
    intro i hi
    obtain rfl : i = 0 := by omega
    show u.mem (u.x 1 + UInt64.ofNat 0) ≠ 0
    rw [mu, x1u, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero, hpb.1]
    decide
  have hlen : (a64Memory P).pathLength u.mem (u.x 1) = 2 :=
    LeanExe.Linux.Memory.pathLength_eq (a64Memory P) u.mem (u.x 1) (n := 1) (by decide) hz hnz
  have hread : readList u.mem (u.x 1) 2 = [46, 0] := by
    simp only [readList, x1u, mu, h1081, hpb.1, hpb.2]
  have hmapO : P.mapped (u.x 1) 2 = true := by
    unfold Platform.mapped
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [x1u, UInt64.add_assoc,
      show (1080 : UInt64) + UInt64.ofNat j = UInt64.ofNat (1080 + j) by rw [UInt64.ofNat_add]; rfl]
    exact hpath j hj
  have hsysO := sysCall_openat (R := R) (P := P)
    (p := ({ p with core := u } : Proc).call (after a 15) svc)
    (by
      rw [Proc.call_mem, Proc.call_x _ _ _ (by decide)]
      show P.mapped (u.x 1) ((a64Memory P).pathLength u.mem (u.x 1)) = true
      rw [hlen]
      exact hmapO)
  simp only [Proc.call_mem, Proc.call_trace] at hsysO
  rw [Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide), Proc.call_x _ _ _ (by decide),
    Proc.call_x _ _ _ (by decide)] at hsysO
  obtain ⟨q2, rq2, pq2, x0q2, -, kq2, spq2, memq2, ioq2, fq2, trq2⟩ := run_callSvc hsvc c15 h15
    hdom (by rw [after_after]; exact hdom _ _ c16) (p := { p with core := u }) pu
    (by show T.find? (fun c => c.arm64 == u.x 8) = _; rw [x8u]; exact hT56) rfl hsysO
  replace x0q2 : q2.core.x 0 = (R p.trace.length).ret := x0q2
  have hev : (⟨LeanExe.Linux.openatCall, [u.x 0, u.x 1, u.x 2, u.x 3],
      [readList u.mem (u.x 1) ((a64Memory P).pathLength u.mem (u.x 1))], [],
      (R p.trace.length).ret, []⟩ : LeanExe.Linux.Event) =
      preopenOpenEvent (G + 1080) (R p.trace.length) := by
    rw [hlen, hread, x0u, x1u, x2u, x3u]
    rfl
  replace trq2 : q2.trace =
      p.trace ++ [Event.sys (preopenOpenEvent (G + 1080) (R p.trace.length))] := by
    rw [trq2, ← hev]
  replace kq2 : ∀ r : Fin 32, r ≠ 0 → r ≠ 30 → q2.core.x r = u.x r := kq2
  replace spq2 : q2.core.sp = u.sp := spq2
  replace ioq2 : q2.core.io = u.io := ioq2
  replace memq2 : q2.core.mem = u.mem := memq2
  have fq2' : q2.fpcr = fpcrValue := by rw [fq2]; exact hfp
  have q12 : ProcReachWith T R P code p q2 := q1.trans rq2
  have pq2' : q2.core.pc = after a 16 := by rw [pq2, after_after]
  have hmem2 : q2.core.mem = preopenMem p.core.mem G false := by
    rw [memq2]
    show u.mem = _
    rw [mu]
    rfl
  -- after the `openat`
  obtain ⟨t, rt, spt, iot, mt, kt, ht⟩ := run_preopenOpened (P := P) hg hcode (s := q2.core)
    pq2'
  rw [x0q2, kq2 19 (by decide) (by decide), x19u] at ht
  have kt' : ∀ r : Fin 32, r ≠ 0 → r ≠ 8 → r ≠ 9 → r ≠ 30 → t.x r = u.x r :=
    fun r h0 h8 h9 h30 => by rw [kt r h8 h9, kq2 r h0 h30]
  -- the exit with status 67 from a state at `after a 37` after a run of the process to `pre`
  have exit : ∀ {v : State} {pre : Proc}, ProcReachWith T R P code p pre →
      pre.fpcr = fpcrValue → Reach P code pre.core v → v.pc = after a 37 → v.io = p.core.io →
      ∃ q, ProcReachWith T R P code p q ∧ q.fpcr = fpcrValue ∧ q.core.io = p.core.io ∧
        q.trace = pre.trace ∧ q.core.pc = base ∧ q.core.x 0 = 67 := by
    intro v pre hpre hfpre rv pv iov
    obtain ⟨w, rw', pw, xw, iow⟩ := run_preopenExit (P := P) hg hcode (s := v) pv
    exact ⟨{ pre with core := w }, hpre.trans (ProcReachWith.of_reach' hdom hfpre (rv.trans rw')
      (by rw [pw]; exact hbase)), hfpre, by rw [← iov]; exact iow, rfl, pw, xw⟩
  have hiot : t.io = p.core.io := by rw [iot, ioq2]; exact iou
  by_cases hbad : (R p.trace.length).ret = 0 - 9 ∨ (R p.trace.length).ret = 0 - 20
  · rw [ite_eq_left hbad] at ht
    refine ⟨{ q2 with core := t }, q12.trans (ProcReachWith.of_reach' hdom fq2' rt
      (by rw [ht]; exact hret)), fq2', hiot, ?_, ?_⟩
    · show q2.trace = _
      rw [trq2, preopenRun, ite_eq_left hbad]
      rfl
    · rw [preopenRun, ite_eq_left hbad]
      refine ⟨ht, by show t.sp = _; rw [spt, spq2]; exact spu, ?_, ?_,
        by show t.mem = _; rw [mt, hmem2]⟩
      · show t.x 17 = _
        rw [kt' 17 (by decide) (by decide) (by decide) (by decide)]
        exact x17u
      · show t.x 18 = _
        rw [kt' 18 (by decide) (by decide) (by decide) (by decide)]
        exact x18u
  rw [ite_eq_right hbad] at ht
  by_cases hd : 4 ≤ (R p.trace.length).ret.toNat ∧ (R p.trace.length).ret.toNat < 2 ^ 31
  swap
  · rw [ite_eq_right hd] at ht
    obtain ⟨q, rq, fq, ioq, trq, pq, xq⟩ := exit q12 fq2' rt ht hiot
    refine ⟨q, rq, fq, ioq, ?_, ?_⟩
    · rw [trq, trq2, preopenRun, ite_eq_right hbad, ite_eq_right hd]
      rfl
    · rw [preopenRun, ite_eq_right hbad, ite_eq_right hd]
      exact ⟨pq, xq⟩
  rw [ite_eq_left hd] at ht
  obtain ⟨pt, x8t⟩ := ht
  -- the `close`
  have q23 : ProcReachWith T R P code q2 { q2 with core := t } :=
    ProcReachWith.of_reach' hdom fq2' rt (by rw [pt]; exact hdom _ _ c28)
  have hsysC := sysCall_close (R := R) (P := P)
    (p := ({ q2 with core := t } : Proc).call (after a 28) svc)
  rw [Proc.call_x _ _ _ (by decide)] at hsysC
  have hx0t : ({ q2 with core := t } : Proc).core.x 0 = (R p.trace.length).ret := by
    show t.x 0 = _
    rw [kt 0 (by decide) (by decide), x0q2]
  have hk2 : (({ q2 with core := t } : Proc).call (after a 28) svc).trace.length =
      p.trace.length + 1 := by
    show q2.trace.length = _
    rw [trq2, List.length_append, List.length_singleton]
  rw [hx0t, hk2] at hsysC
  obtain ⟨q4, rq4, pq4, x0q4, -, kq4, spq4, memq4, ioq4, fq4, trq4⟩ := run_callSvc hsvc c28 h28
    hdom (by rw [after_after]; exact hdom _ _ c29) (p := { q2 with core := t }) pt
    (by show T.find? (fun c => c.arm64 == t.x 8) = _; rw [x8t]; exact hT57) rfl hsysC
  replace x0q4 : q4.core.x 0 = (R (p.trace.length + 1)).ret := x0q4
  replace trq4 : q4.trace = q2.trace ++
      [Event.sys (preopenCloseEvent (R p.trace.length).ret (R (p.trace.length + 1)))] := trq4
  have fq4' : q4.fpcr = fpcrValue := by rw [fq4]; exact fq2'
  have q14 : ProcReachWith T R P code p q4 := q12.trans (q23.trans rq4)
  have pq4' : q4.core.pc = after a 29 := by rw [pq4, after_after]
  have kq4' : ∀ r : Fin 32, r ≠ 0 → r ≠ 8 → r ≠ 9 → r ≠ 30 → q4.core.x r = u.x r :=
    fun r h0 h8 h9 h30 => by rw [kq4 r h0 h30]; exact kt' r h0 h8 h9 h30
  have x16q4 : q4.core.x 20 = G := by
    rw [kq4' 20 (by decide) (by decide) (by decide) (by decide)]
    exact x16u
  obtain ⟨w, rw', spw, iow, kw, hw⟩ := run_preopenClosed (P := P) hg hcode (s := q4.core) pq4'
    hU (by rw [x16q4]; exact hflag) (by rw [x16q4]; exact hheld)
  rw [x0q4] at hw
  have htr4 : q4.trace = p.trace ++ (preopenRun (G + 1080) R p.trace.length).1.map Event.sys := by
    rw [trq4, trq2, preopenRun, ite_eq_right hbad, ite_eq_left hd]
    split <;> simp
  have hiow : w.io = p.core.io := by
    rw [iow, ioq4]
    show t.io = _
    exact hiot
  by_cases hok : (R (p.trace.length + 1)).ret = 0 ∨
      LeanExe.Linux.isError (R (p.trace.length + 1)).ret = true
  · rw [ite_eq_left hok, x16q4, kq4' 19 (by decide) (by decide) (by decide) (by decide), x19u] at hw
    obtain ⟨pw, mw⟩ := hw
    refine ⟨{ q4 with core := w }, q14.trans (ProcReachWith.of_reach' hdom fq4' rw'
      (by rw [pw]; exact hret)), fq4', hiow, htr4, ?_⟩
    rw [preopenRun, ite_eq_right hbad, ite_eq_left hd, ite_eq_left hok]
    refine ⟨pw, ?_, ?_, ?_, ?_⟩
    · show w.sp = _
      rw [spw, spq4]
      show t.sp = _
      rw [spt, spq2]
      exact spu
    · show w.x 17 = _
      rw [kw 17 (by decide), kq4' 17 (by decide) (by decide) (by decide) (by decide)]
      exact x17u
    · show w.x 18 = _
      rw [kw 18 (by decide), kq4' 18 (by decide) (by decide) (by decide) (by decide)]
      exact x18u
    · show w.mem = _
      rw [mw, memq4]
      show store8 (store8 t.mem (G + 8) 1) (G + 19) 1 = _
      rw [mt, hmem2]
      rfl
  · rw [ite_eq_right hok] at hw
    obtain ⟨pw, -⟩ := hw
    obtain ⟨q, rq, fq, ioq, trq, pq, xq⟩ := exit q14 fq4' rw' pw hiow
    refine ⟨q, rq, fq, ioq, by rw [trq, htr4], ?_⟩
    rw [preopenRun, ite_eq_right hbad, ite_eq_left hd, ite_eq_right hok]
    exact ⟨pq, xq⟩

end Check

end LeanExe.A64
