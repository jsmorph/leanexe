import LeanExe.A64.Proof.WasiFiles
import LeanExe.A64.Proof.WasiPath

/-!
The stub of `path_open` of `LeanExe/A64/WasiFiles.lean` in the program's model: its pieces at
their offsets and the runs of the instructions between them.  `openStub_code` places each piece
of `openStub` at its offset, with the lengths of `utf8Check` and `openHow` from
`utf8Check_length` and `openHow_length`.  `run_openHead` follows the stub from its entry, which
keeps the result's pointer in X21 and the return address in X19 and sets X16 to the scratch,
through the range checks of the path and of the result's four bytes to the trap stub or to the
check of UTF-8 at offset 17.

`run_openFlags` follows the tests of the `fdflags` and the `oflags` at offset 96 to the return of
errno 58 or 28 or to the zero scan at offset 105, and `run_openLength` the test of the path's
length at offset 115 to the return of errno 37 or to the copy of the path at offset 117.  The
runs of the other pieces are those of `LeanExe/A64/Proof/WasiPreopen.lean`,
`LeanExe/A64/Proof/WasiUtf8.lean`, `LeanExe/A64/Proof/WasiPath.lean`,
`Verified/ShimA64/OpenHow.lean`, and `LeanExe/A64/Proof/WasiFiles.lean`, and
`Verified/ShimA64/Open.lean` composes them.
-/

namespace LeanExe.A64

/-! ## The generator's parts -/

theorem utf8Check_length {a bad : UInt64} {is : List Instr} (hg : utf8Check a bad = .ok is) :
    is.length = 74 := by
  unfold utf8Check at hg
  simp only [bind, Except.bind, pure, Except.pure] at hg
  repeat' split at hg
  all_goals (cases hg <;> rfl)

theorem openHow_length {a : UInt64} {is : List Instr} (hg : openHow a = .ok is) :
    is.length = 60 := by
  unfold openHow at hg
  simp only [bind, Except.bind, pure, Except.pure] at hg
  repeat' split at hg
  all_goals (cases hg <;> rfl)

theorem openStub_ok {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) :
    ∃ r1 r2 utf8 held zero copy how calls result g98 g101 g104 g116,
      rangeCheck (after a 8) tr = .ok r1 ∧ rangeCheck (after a 13) tr = .ok r2 ∧
      utf8Check (after a 17) (after a 226) = .ok utf8 ∧
      heldTest (after a 91) (after a 228) 0 = .ok held ∧
      zeroScan (after a 105) (after a 232) = .ok zero ∧ pathCopy (after a 117) = .ok copy ∧
      openHow (after a 130) = .ok how ∧ openCalls (after a 190) svc = .ok calls ∧
      openResult (after a 204) tr en = .ok result ∧
      cbField (after a 98) (after a 230) = .ok g98 ∧
      cbField (after a 101) (after a 105) = .ok g101 ∧
      cbField (after a 104) (after a 232) = .ok g104 ∧
      cbField (after a 116) (after a 234) = .ok g116 ∧
      is = [.orrReg 21 31 8, .orrReg 19 31 30] ++ scratchAddr sc ++ [.addReg 12 2 3] ++ r1 ++
        [.addImm 12 21 4] ++ r2 ++ utf8 ++ held ++
        [.movz 9 0x1A 0, .andReg 9 7 9, .cbnz 9 g98, .movz 9 2 0, .andReg 9 4 9, .cbz 9 g101,
          .movz 9 0xD 0, .andReg 9 4 9, .cbnz 9 g104] ++ zero ++
        [.subsImm 31 3 4095, .bcond 8 g116] ++ copy ++ how ++ calls ++ result ++
        [.movz 0 25 0, .ret 30, .movz 0 8 0, .ret 30, .movz 0 58 0, .ret 30, .movz 0 28 0,
          .ret 30, .movz 0 37 0, .ret 30] := by
  unfold openStub at hg
  cases h1 : rangeCheck (after a 8) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok r1 =>
  cases h2 : rangeCheck (after a 13) tr with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok r2 =>
  cases hu : utf8Check (after a 17) (after a 226) with
  | error err => simp [h1, h2, hu, bind, Except.bind] at hg
  | ok utf8 =>
  cases hh : heldTest (after a 91) (after a 228) 0 with
  | error err => simp [h1, h2, hu, hh, bind, Except.bind] at hg
  | ok held =>
  cases hz : zeroScan (after a 105) (after a 232) with
  | error err => simp [h1, h2, hu, hh, hz, bind, Except.bind] at hg
  | ok zero =>
  cases hc : pathCopy (after a 117) with
  | error err => simp [h1, h2, hu, hh, hz, hc, bind, Except.bind] at hg
  | ok copy =>
  cases hw : openHow (after a 130) with
  | error err => simp [h1, h2, hu, hh, hz, hc, hw, bind, Except.bind] at hg
  | ok how =>
  cases hl : openCalls (after a 190) svc with
  | error err => simp [h1, h2, hu, hh, hz, hc, hw, hl, bind, Except.bind] at hg
  | ok calls =>
  cases hr : openResult (after a 204) tr en with
  | error err => simp [h1, h2, hu, hh, hz, hc, hw, hl, hr, bind, Except.bind] at hg
  | ok result =>
  cases f98 : cbField (after a 98) (after a 230) with
  | error err => simp [h1, h2, hu, hh, hz, hc, hw, hl, hr, f98, bind, Except.bind] at hg
  | ok g98 =>
  cases f101 : cbField (after a 101) (after a 105) with
  | error err => simp [h1, h2, hu, hh, hz, hc, hw, hl, hr, f98, f101, bind, Except.bind] at hg
  | ok g101 =>
  cases f104 : cbField (after a 104) (after a 232) with
  | error err =>
    simp [h1, h2, hu, hh, hz, hc, hw, hl, hr, f98, f101, f104, bind, Except.bind] at hg
  | ok g104 =>
  cases f116 : cbField (after a 116) (after a 234) with
  | error err =>
    simp [h1, h2, hu, hh, hz, hc, hw, hl, hr, f98, f101, f104, f116, bind, Except.bind] at hg
  | ok g116 =>
  simp only [h1, h2, hu, hh, hz, hc, hw, hl, hr, f98, f101, f104, f116, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq] at hg
  exact ⟨r1, r2, utf8, held, zero, copy, how, calls, result, g98, g101, g104, g116, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg.symm⟩

theorem openStub_length {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) : is.length = openStubSize := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, hu, hh, hz, hc, hw, hl, hr, -, -, -, -,
    rfl⟩ := openStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok h1
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok h2
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh
  obtain ⟨_, _, _, _, _, _, rfl⟩ := zeroScan_ok hz
  obtain ⟨_, _, _, _, rfl⟩ := pathCopy_ok hc
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := openCalls_ok hl
  obtain ⟨_, _, _, ht, rfl⟩ := openResult_ok hr
  obtain ⟨_, _, _, _, rfl⟩ := errnoTail_ok ht
  simp [utf8Check_length hu, openHow_length hw, scratchAddr, movImm, wordStore, openStubSize]

section Runs

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- Each piece of the stub of `path_open` at its offset. -/
theorem openStub_code {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) :
    ∃ r1 r2 utf8 held zero copy how calls result g98 g101 g104 g116,
      rangeCheck (after a 8) tr = .ok r1 ∧ rangeCheck (after a 13) tr = .ok r2 ∧
      utf8Check (after a 17) (after a 226) = .ok utf8 ∧
      heldTest (after a 91) (after a 228) 0 = .ok held ∧
      zeroScan (after a 105) (after a 232) = .ok zero ∧ pathCopy (after a 117) = .ok copy ∧
      openHow (after a 130) = .ok how ∧ openCalls (after a 190) svc = .ok calls ∧
      openResult (after a 204) tr en = .ok result ∧
      cbField (after a 98) (after a 230) = .ok g98 ∧
      cbField (after a 101) (after a 105) = .ok g101 ∧
      cbField (after a 104) (after a 232) = .ok g104 ∧
      cbField (after a 116) (after a 234) = .ok g116 ∧
      CodeAt code a [.orrReg 21 31 8, .orrReg 19 31 30] ∧
      CodeAt code (after a 2) (scratchAddr sc) ∧ CodeAt code (after a 7) [.addReg 12 2 3] ∧
      CodeAt code (after a 8) r1 ∧ CodeAt code (after a 12) [.addImm 12 21 4] ∧
      CodeAt code (after a 13) r2 ∧ CodeAt code (after a 17) utf8 ∧
      CodeAt code (after a 91) held ∧
      CodeAt code (after a 96) [.movz 9 0x1A 0, .andReg 9 7 9, .cbnz 9 g98, .movz 9 2 0,
        .andReg 9 4 9, .cbz 9 g101, .movz 9 0xD 0, .andReg 9 4 9, .cbnz 9 g104] ∧
      CodeAt code (after a 105) zero ∧
      CodeAt code (after a 115) [.subsImm 31 3 4095, .bcond 8 g116] ∧
      CodeAt code (after a 117) copy ∧ CodeAt code (after a 130) how ∧
      CodeAt code (after a 190) calls ∧ CodeAt code (after a 204) result ∧
      CodeAt code (after a 226) [.movz 0 25 0, .ret 30] ∧
      CodeAt code (after a 228) [.movz 0 8 0, .ret 30] ∧
      CodeAt code (after a 230) [.movz 0 58 0, .ret 30] ∧
      CodeAt code (after a 232) [.movz 0 28 0, .ret 30] ∧
      CodeAt code (after a 234) [.movz 0 37 0, .ret 30] := by
  obtain ⟨r1, r2, utf8, held, zero, copy, how, calls, result, g98, g101, g104, g116, h1, h2, hu,
    hh, hz, hc, hw, hl, hr, f98, f101, f104, f116, rfl⟩ := openStub_ok hg
  have l1 : r1.length = 4 := by obtain ⟨_, _, rfl⟩ := rangeCheck_ok h1; rfl
  have l2 : r2.length = 4 := by obtain ⟨_, _, rfl⟩ := rangeCheck_ok h2; rfl
  have lu := utf8Check_length hu
  have lh : held.length = 5 := by obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh; rfl
  have lz : zero.length = 10 := by obtain ⟨_, _, _, _, _, _, rfl⟩ := zeroScan_ok hz; rfl
  have lc : copy.length = 13 := by obtain ⟨_, _, _, _, rfl⟩ := pathCopy_ok hc; rfl
  have lw := openHow_length hw
  have ll : calls.length = 14 := by
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := openCalls_ok hl
    rfl
  have lr : result.length = 22 := by
    obtain ⟨_, _, _, ht, rfl⟩ := openResult_ok hr
    obtain ⟨_, _, _, _, rfl⟩ := errnoTail_ok ht
    rfl
  have ls : (scratchAddr sc).length = 5 := rfl
  have cE := CodeAt.split code hcode (n := 226) (by simp [ls, l1, l2, lu, lh, lz, lc, lw, ll, lr])
  have cR := CodeAt.split code cE.1 (n := 204) (by simp [ls, l1, l2, lu, lh, lz, lc, lw, ll])
  have cL := CodeAt.split code cR.1 (n := 190) (by simp [ls, l1, l2, lu, lh, lz, lc, lw])
  have cW := CodeAt.split code cL.1 (n := 130) (by simp [ls, l1, l2, lu, lh, lz, lc])
  have cC := CodeAt.split code cW.1 (n := 117) (by simp [ls, l1, l2, lu, lh, lz])
  have cN := CodeAt.split code cC.1 (n := 115) (by simp [ls, l1, l2, lu, lh, lz])
  have cZ := CodeAt.split code cN.1 (n := 105) (by simp [ls, l1, l2, lu, lh])
  have cF := CodeAt.split code cZ.1 (n := 96) (by simp [ls, l1, l2, lu, lh])
  have cH := CodeAt.split code cF.1 (n := 91) (by simp [ls, l1, l2, lu])
  have cU := CodeAt.split code cH.1 (n := 17) (by simp [ls, l1, l2])
  have c2 := CodeAt.split code cU.1 (n := 13) (by simp [ls, l1])
  have c12 := CodeAt.split code c2.1 (n := 12) (by simp [ls, l1])
  have c1 := CodeAt.split code c12.1 (n := 8) (by simp [ls])
  have c7 := CodeAt.split code c1.1 (n := 7) (by simp [ls])
  have cS := CodeAt.split code c7.1 (n := 2) rfl
  have e25 : CodeAt code (after a 226) [.movz 0 25 0, .ret 30] := by
    simpa [after_after] using CodeAt.drop_take code cE.2 0 2 (by simp)
  have e8 : CodeAt code (after a 228) [.movz 0 8 0, .ret 30] := by
    simpa [after_after] using CodeAt.drop_take code cE.2 2 2 (by simp)
  have e58 : CodeAt code (after a 230) [.movz 0 58 0, .ret 30] := by
    simpa [after_after] using CodeAt.drop_take code cE.2 4 2 (by simp)
  have e28 : CodeAt code (after a 232) [.movz 0 28 0, .ret 30] := by
    simpa [after_after] using CodeAt.drop_take code cE.2 6 2 (by simp)
  have e37 : CodeAt code (after a 234) [.movz 0 37 0, .ret 30] := by
    simpa [after_after] using CodeAt.drop_take code cE.2 8 2 (by simp)
  exact ⟨r1, r2, utf8, held, zero, copy, how, calls, result, g98, g101, g104, g116, h1, h2, hu,
    hh, hz, hc, hw, hl, hr, f98, f101, f104, f116, cS.1, cS.2, c7.2, c1.2, c12.2, c2.2, cU.2,
    cH.2, cF.2, cZ.2, cN.2, cC.2, cW.2, cL.2, cR.2, e25, e8, e58, e28, e37⟩

/-- `MOVZ X9, #m` and `AND X9, Xr, X9`: X9 holds X`r` masked by `m`. -/
theorem run_mask9 {a : UInt64} {r : Fin 32} {m : Fin 65536} (hr : r ≠ 9)
    (hcode : CodeAt code a [.movz 9 m 0, .andReg 9 r 9]) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = after a 2 ∧ t.x 9 = s.x r &&& UInt64.ofNat m.val ∧
      (∀ q : Fin 32, q ≠ 9 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movz P code (s := s) (d := 9) (v := m)
    (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_setX P code (s := u1) (d := 9)
    (v := u1.x r &&& u1.x 9) (by decide) (by rw [q1]; exact c1) rfl
  exact ⟨u2, r1.trans r2, by rw [p2, q1, ← after_succ], by rw [x2, x1, k1 r hr],
    fun q hq => by rw [k2 q hq, k1 q hq], by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩

/-- The head of the stub of `path_open`, from its entry: X21 at the result's pointer in X8, X19 at
the return address, and X16 at the scratch, `sc` bytes above the area, and then the trap stub `tr`
when the path's end, X2 plus X3, or the result's end, X8 plus 4, exceeds the memory's size, 8 plus
the area's first word, and the check of UTF-8 at `after a 17` otherwise.  X12 and X13 change too,
and the memory, SP, and the UART's state keep their values. -/
theorem run_openHead {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = a) (hsize : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧
      (t.pc = if load64 s.mem (s.x 17) + 8 < s.x 2 + s.x 3 ∨
          load64 s.mem (s.x 17) + 8 < s.x 8 + 4 then tr else after a 17) ∧
      t.x 16 = s.x 17 + UInt64.ofNat sc ∧ t.x 19 = s.x 30 ∧ t.x 21 = s.x 8 ∧
      (∀ q : Fin 32, q ≠ 12 → q ≠ 13 → q ≠ 16 → q ≠ 19 → q ≠ 21 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨r1, r2, _, _, _, _, _, _, _, _, _, _, _, h1, h2, -, -, -, -, -, -, -, -, -, -, -, c0,
    cS, c7, cR1, c12, cR2, -⟩ := openStub_code code hg hcode
  obtain ⟨f1, hf1, rfl⟩ := rangeCheck_ok h1
  obtain ⟨f2, hf2, rfl⟩ := rangeCheck_ok h2
  have i0 := c0 0 (by simp)
  have i1 := c0 1 (by simp)
  have i7 := c7 0 (by simp)
  have i12 := c12 0 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at i0 i1 i7 i12
  obtain ⟨u1, r1', p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 21) (m := 8)
    (by decide) (by rw [hpc]; exact i0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2', p2, x2, k2, sp2, m2, io2⟩ := step_mov P code (s := u1) (d := 19) (m := 30)
    (by decide) (by rw [q1]; exact i1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_scratchAddr P code cS q2
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addReg P code (s := u3) (d := 12) (n := 2)
    (m := 3) (by decide) (by rw [p3, after_after]; exact i7)
  have q4 : u4.pc = after a 8 := by rw [p4, p3, after_after, ← after_succ]
  have e17 : u4.x 17 = s.x 17 := by
    rw [k4 17 (by decide), k3 17 (by decide), k2 17 (by decide), k1 17 (by decide)]
  have e12 : u4.x 12 = s.x 2 + s.x 3 := by
    rw [x4, k3 2 (by decide), k3 3 (by decide), k2 2 (by decide), k2 3 (by decide),
      k1 2 (by decide), k1 3 (by decide)]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_rangeCheck P code cR1 hf1 q4
    (fun k hk => by rw [e17]; exact hsize k hk)
  rw [m4, m3, m2, m1, e17, e12] at p5
  have k15 : ∀ q : Fin 32, q ≠ 12 → q ≠ 13 → q ≠ 16 → q ≠ 19 → q ≠ 21 → u5.x q = s.x q :=
    fun q h12 h13 h16 h19 h21 => by rw [k5 q h13, k4 q h12, k3 q h16, k2 q h19, k1 q h21]
  have x16_5 : u5.x 16 = s.x 17 + UInt64.ofNat sc := by
    rw [k5 16 (by decide), k4 16 (by decide), x3, k2 17 (by decide), k1 17 (by decide)]
  have x19_5 : u5.x 19 = s.x 30 := by
    rw [k5 19 (by decide), k4 19 (by decide), k3 19 (by decide), x2, k1 30 (by decide)]
  have x21_5 : u5.x 21 = s.x 8 := by
    rw [k5 21 (by decide), k4 21 (by decide), k3 21 (by decide), k2 21 (by decide), x1]
  have r15 : Reach P code s u5 := r1'.trans (r2'.trans (r3.trans (r4.trans r5)))
  have sp15 : u5.sp = s.sp := by rw [sp5, sp4, sp3, sp2, sp1]
  have m15 : u5.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  have io15 : u5.io = s.io := by rw [io5, io4, io3, io2, io1]
  by_cases hb1 : load64 s.mem (s.x 17) + 8 < s.x 2 + s.x 3
  · rw [ite_eq_left hb1] at p5
    exact ⟨u5, r15, by rw [p5, ite_eq_left (Or.inl hb1)], x16_5, x19_5, x21_5, k15, sp15, m15,
      io15⟩
  rw [ite_eq_right hb1, after_after] at p5
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_addImm P code (s := u5) (d := 12) (n := 21)
    (imm := 4) (by decide) (by decide) (by rw [p5]; exact i12)
  have q6 : u6.pc = after a 13 := by rw [p6, p5, ← after_succ]
  have e17' : u6.x 17 = s.x 17 := by
    rw [k6 17 (by decide), k15 17 (by decide) (by decide) (by decide) (by decide) (by decide)]
  have e12' : u6.x 12 = s.x 8 + 4 := by
    rw [x6, x21_5]
    rfl
  obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := run_rangeCheck P code cR2 hf2 q6
    (fun k hk => by rw [e17']; exact hsize k hk)
  rw [m6, m15, e17', e12'] at p7
  refine ⟨u7, r15.trans (r6.trans r7), ?_, ?_, ?_, ?_,
    fun q h12 h13 h16 h19 h21 => by rw [k7 q h13, k6 q h12, k15 q h12 h13 h16 h19 h21],
    by rw [sp7, sp6, sp15], by rw [m7, m6, m15], by rw [io7, io6, io15]⟩
  · rw [p7]
    by_cases hb2 : load64 s.mem (s.x 17) + 8 < s.x 8 + 4
    · rw [ite_eq_left hb2, ite_eq_left (Or.inr hb2)]
    · rw [ite_eq_right hb2, ite_eq_right (fun h => h.elim hb1 hb2), after_after]
  · rw [k7 16 (by decide), k6 16 (by decide), x16_5]
  · rw [k7 19 (by decide), k6 19 (by decide), x19_5]
  · rw [k7 21 (by decide), k6 21 (by decide), x21_5]

/-- The tests of the flags of `path_open`, from `after a 96`: the return of errno 58 when the
`fdflags` in X7 hold `dsync`, `rsync`, or `sync`, the return of errno 28 when the `oflags` in X4
hold `directory` with `creat`, `excl`, or `trunc`, and the zero scan at `after a 105` otherwise.
X9 changes, and the memory, SP, and the UART's state keep their values. -/
theorem run_openFlags {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 96) :
    ∃ t, Reach P code s t ∧ (∀ q : Fin 32, q ≠ 0 → q ≠ 9 → t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io ∧
      if s.x 7 &&& 0x1A ≠ 0 then t.pc = s.x 30 ∧ t.x 0 = 58
      else if s.x 4 &&& 2 ≠ 0 ∧ s.x 4 &&& 0xD ≠ 0 then t.pc = s.x 30 ∧ t.x 0 = 28
      else t.pc = after a 105 ∧ t.x 0 = s.x 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, g98, g101, g104, _, -, -, -, -, -, -, -, -, -, f98, f101,
    f104, -, -, -, -, -, -, -, -, -, cF, -, -, -, -, -, -, -, -, e58, e28, -⟩ :=
    openStub_code code hg hcode
  have cA : CodeAt code (after a 96) [.movz 9 0x1A 0, .andReg 9 7 9] := by
    simpa [after_after] using CodeAt.drop_take code cF 0 2 (by simp)
  have cB : CodeAt code (after a 99) [.movz 9 2 0, .andReg 9 4 9] := by
    simpa [after_after] using CodeAt.drop_take code cF 3 2 (by simp)
  have cC : CodeAt code (after a 102) [.movz 9 0xD 0, .andReg 9 4 9] := by
    simpa [after_after] using CodeAt.drop_take code cF 6 2 (by simp)
  have i2 := cF 2 (by simp)
  have i5 := cF 5 (by simp)
  have i8 := cF 8 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at i2 i5 i8
  -- the `fdflags`
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_mask9 P code (r := 7) (by decide) cA hpc
  rw [show UInt64.ofNat (0x1A : Fin 65536).val = 0x1A from rfl] at x1
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbnz P code (s := u1) (r := 9) (g := g98)
    (target := after a 230) (by rw [p1, after_after]; exact i2)
    (by rw [p1, after_after]; exact cbField_target f98)
  rw [x1, p1, after_after] at p2
  by_cases hf : s.x 7 &&& 0x1A ≠ 0
  · rw [ite_eq_left hf] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_movzRet P code e58 p2
    refine ⟨u3, r1.trans (r2.trans r3), fun q h0 h9 => by rw [k3 q h0, k2, k1 q h9],
      by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1], ?_⟩
    rw [ite_eq_left hf]
    exact ⟨by rw [p3, k2, k1 30 (by decide)], x3.trans rfl⟩
  rw [ite_eq_right hf, ← after_succ] at p2
  -- the `oflags`
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_mask9 P code (r := 4) (by decide) cB p2
  rw [show UInt64.ofNat (2 : Fin 65536).val = 2 from rfl, k2, k1 4 (by decide)] at x3
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := step_cbz P code (s := u3) (r := 9) (g := g101)
    (target := after a 105) (by rw [p3, after_after]; exact i5)
    (by rw [p3, after_after]; exact cbField_target f101)
  rw [x3, p3, after_after] at p4
  have kk4 : ∀ q : Fin 32, q ≠ 9 → u4.x q = s.x q := fun q h9 => by
    rw [k4, k3 q h9, k2, k1 q h9]
  have r14 : Reach P code s u4 := r1.trans (r2.trans (r3.trans r4))
  have sp14 : u4.sp = s.sp := by rw [sp4, sp3, sp2, sp1]
  have m14 : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  have io14 : u4.io = s.io := by rw [io4, io3, io2, io1]
  by_cases h2 : s.x 4 &&& 2 = 0
  · rw [ite_eq_left h2] at p4
    refine ⟨u4, r14, fun q _ h9 => kk4 q h9, sp14, m14, io14, ?_⟩
    rw [ite_eq_right hf, ite_eq_right (fun h => h.1 h2)]
    exact ⟨p4, kk4 0 (by decide)⟩
  rw [ite_eq_right h2, ← after_succ] at p4
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_mask9 P code (r := 4) (by decide) cC p4
  rw [show UInt64.ofNat (0xD : Fin 65536).val = 0xD from rfl, kk4 4 (by decide)] at x5
  obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := step_cbnz P code (s := u5) (r := 9) (g := g104)
    (target := after a 232) (by rw [p5, after_after]; exact i8)
    (by rw [p5, after_after]; exact cbField_target f104)
  rw [x5, p5, after_after] at p6
  have kk6 : ∀ q : Fin 32, q ≠ 9 → u6.x q = s.x q := fun q h9 => by rw [k6, k5 q h9, kk4 q h9]
  have r16 : Reach P code s u6 := r14.trans (r5.trans r6)
  by_cases hd : s.x 4 &&& 0xD ≠ 0
  · rw [ite_eq_left hd] at p6
    obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := run_movzRet P code e28 p6
    refine ⟨u7, r16.trans r7, fun q h0 h9 => by rw [k7 q h0, kk6 q h9],
      by rw [sp7, sp6, sp5, sp14], by rw [m7, m6, m5, m14], by rw [io7, io6, io5, io14], ?_⟩
    rw [ite_eq_right hf, ite_eq_left ⟨h2, hd⟩]
    exact ⟨by rw [p7, kk6 30 (by decide)], x7.trans rfl⟩
  · rw [ite_eq_right hd, ← after_succ] at p6
    refine ⟨u6, r16, fun q _ h9 => kk6 q h9, by rw [sp6, sp5, sp14], by rw [m6, m5, m14],
      by rw [io6, io5, io14], ?_⟩
    rw [ite_eq_right hf, ite_eq_right (fun h => hd h.2)]
    exact ⟨p6, kk6 0 (by decide)⟩

/-- The test of the path's length in X3, from `after a 115`: the return of errno 37 for 4,096
bytes or more, and the copy of the path at `after a 117` otherwise.  The memory, SP, and the
UART's state keep their values. -/
theorem run_openLength {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : openStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 115) :
    ∃ t, Reach P code s t ∧ (∀ q : Fin 32, q ≠ 0 → t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = s.io ∧
      if 4095 < s.x 3 then t.pc = s.x 30 ∧ t.x 0 = 37 else t.pc = after a 117 ∧ t.x 0 = s.x 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, g116, -, -, -, -, -, -, -, -, -, -, -, -, f116, -,
    -, -, -, -, -, -, -, -, -, cN, -, -, -, -, -, -, -, -, e37⟩ := openStub_code code hg hcode
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiImm P code (r := 3) (imm := 4095)
    (tB := after a 234) (by decide) cN (by rw [after_after]; exact cbField_target f116) hpc
  rw [show UInt64.ofNat (4095 : Fin 4096).val = 4095 from rfl] at p1
  by_cases hl : 4095 < s.x 3
  · rw [ite_eq_left hl] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzRet P code e37 p1
    refine ⟨u2, r1.trans r2, fun q h0 => by rw [k2 q h0, k1], by rw [sp2, sp1], by rw [m2, m1],
      by rw [io2, io1], ?_⟩
    rw [ite_eq_left hl]
    exact ⟨by rw [p2, k1], x2.trans rfl⟩
  · rw [ite_eq_right hl, after_after] at p1
    refine ⟨u1, r1, fun q _ => k1 q, sp1, m1, io1, ?_⟩
    rw [ite_eq_right hl]
    exact ⟨p1, k1 0⟩

end Runs

end LeanExe.A64
