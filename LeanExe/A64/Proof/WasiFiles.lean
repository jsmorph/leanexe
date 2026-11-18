import LeanExe.A64.Proof.WasiPreopen
import LeanExe.A64.Proof.WasiClocks
import LeanExe.A64.WasiFiles

/-!
The runs of the parts of the stubs of `LeanExe/A64/WasiFiles.lean` in the program's model.
`run_errnoTail` returns the errno of a negated error number in X0 or reaches the trap stub,
`run_wordStore` stores the low 32 bits of X0 at a guest address in a register, and
`run_countTail` stores a count at most the length in X11 at the count's pointer in X3 or hands the
result to `run_errnoTail`.  `run_closeFront` follows the stub of `fd_close` from its entry to the
return of errno 8 for a descriptor that the shim does not hold or to the call of `close`, and
`run_closeBack` from the call's result through the clearing of the descriptor's byte and of the
preopen flag to the return or the trap stub.  `run_handleFront` follows the stub of `fd_read` or
`fd_write` on a handle from its entry to the trap stub, to the return of errno 8, or to the call,
whose result `run_countTail` handles.
-/

namespace LeanExe.A64

open Wasm

/-! ## The generator's parts -/


theorem countTail_ok {a tr en : UInt64} {is : List Instr} (hg : countTail a tr en = .ok is) :
    ∃ g1 tail, cbField (after a 1) (after a 13) = .ok g1 ∧ errorTail (after a 13) tr en = .ok tail ∧
      is = [.subsReg 31 0 11, .bcond 8 g1] ++ wordStore 3 ++ [.movz 0 0 0, .ret 19] ++ tail := by
  unfold countTail at hg
  cases ht : errorTail (after a 13) tr en with
  | error err => simp [ht, bind, Except.bind] at hg
  | ok tail =>
  cases h1 : cbField (after a 1) (after a 13) with
  | error err => simp [ht, h1, bind, Except.bind] at hg
  | ok g1 =>
  simp only [ht, h1, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, tail, rfl, rfl, hg.symm⟩

theorem closeStub_ok {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : closeStub a svc tr en sc = .ok is) :
    ∃ held tail g13 g17 g19, heldTest (after a 5) (after a 28) 0 = .ok held ∧
      errorTail (after a 20) tr en = .ok tail ∧ bField (after a 13) svc = .ok g13 ∧
      cbField (after a 17) (after a 19) = .ok g17 ∧ cbField (after a 19) (after a 26) = .ok g19 ∧
      is = scratchAddr sc ++ held ++
        [.orrReg 19 31 30, .orrReg 21 31 0, .movz 8 57 0, .bl g13, .addReg 10 20 21,
          .strb 31 10 16, .subsImm 31 21 3, .bcond 1 g17, .strb 31 20 8, .cbz 0 g19] ++ tail ++
        [.movz 0 0 0, .ret 19, .movz 0 8 0, .ret 30] := by
  unfold closeStub at hg
  cases hh : heldTest (after a 5) (after a 28) 0 with
  | error err => simp [hh, bind, Except.bind] at hg
  | ok held =>
  cases ht : errorTail (after a 20) tr en with
  | error err => simp [hh, ht, bind, Except.bind] at hg
  | ok tail =>
  cases h13 : bField (after a 13) svc with
  | error err => simp [hh, ht, h13, bind, Except.bind] at hg
  | ok g13 =>
  cases h17 : cbField (after a 17) (after a 19) with
  | error err => simp [hh, ht, h13, h17, bind, Except.bind] at hg
  | ok g17 =>
  cases h19 : cbField (after a 19) (after a 26) with
  | error err => simp [hh, ht, h13, h17, h19, bind, Except.bind] at hg
  | ok g19 =>
  simp only [hh, ht, h13, h17, h19, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨held, tail, g13, g17, g19, rfl, rfl, rfl, rfl, rfl, hg.symm⟩

theorem handleStub_ok {nr : Fin 65536} {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : handleStub nr a svc tr en sc = .ok is) :
    ∃ r1 r2 r3 held tail g1 g39, rangeCheck (after a 3) tr = .ok r1 ∧
      rangeCheck (after a 12) tr = .ok r2 ∧ rangeCheck (after a 17) tr = .ok r3 ∧
      heldTest (after a 26) (after a 59) 0 = .ok held ∧ countTail (after a 40) tr en = .ok tail ∧
      cbField (after a 1) tr = .ok g1 ∧ bField (after a 39) svc = .ok g39 ∧
      is = [.subsImm 31 2 1, .bcond 1 g1, .addImm 12 1 8] ++ r1 ++
        [.addReg 14 17 1, .ldr 14 14 512, .orrW 9 31 14, .lsrImm 12 14 32, .addReg 12 9 12] ++
        r2 ++ [.addImm 12 3 4] ++ r3 ++ scratchAddr sc ++ held ++
        [.orrW 10 31 14, .lsrImm 11 14 32, .addReg 1 17 10, .addImm 1 1 4095, .addImm 1 1 1,
          .orrReg 2 31 11, .movz 8 nr 0, .orrReg 19 31 30, .bl g39] ++ tail ++
        [.movz 0 8 0, .ret 30] := by
  unfold handleStub at hg
  cases h1 : rangeCheck (after a 3) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok r1 =>
  cases h2 : rangeCheck (after a 12) tr with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok r2 =>
  cases h3 : rangeCheck (after a 17) tr with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok r3 =>
  cases hh : heldTest (after a 26) (after a 59) 0 with
  | error err => simp [h1, h2, h3, hh, bind, Except.bind] at hg
  | ok held =>
  cases ht : countTail (after a 40) tr en with
  | error err => simp [h1, h2, h3, hh, ht, bind, Except.bind] at hg
  | ok tail =>
  cases hb : cbField (after a 1) tr with
  | error err => simp [h1, h2, h3, hh, ht, hb, bind, Except.bind] at hg
  | ok g1 =>
  cases hl : bField (after a 39) svc with
  | error err => simp [h1, h2, h3, hh, ht, hb, hl, bind, Except.bind] at hg
  | ok g39 =>
  simp only [h1, h2, h3, hh, ht, hb, hl, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  exact ⟨r1, r2, r3, held, tail, g1, g39, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg.symm⟩

theorem closeStub_length {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : closeStub a svc tr en sc = .ok is) : is.length = closeStubSize := by
  obtain ⟨held, tail, g13, g17, g19, hh, ht, -, -, -, rfl⟩ := closeStub_ok hg
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh
  obtain ⟨_, _, _, _, rfl⟩ := errorTail_ok ht
  rfl

theorem handleStub_length {nr : Fin 65536} {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : handleStub nr a svc tr en sc = .ok is) : is.length = handleStubSize := by
  obtain ⟨r1, r2, r3, held, tail, g1, g39, h1, h2, h3, hh, ht, -, -, rfl⟩ := handleStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok h1
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok h2
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok h3
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok hh
  obtain ⟨_, tail', _, ht', rfl⟩ := countTail_ok ht
  obtain ⟨_, _, _, _, rfl⟩ := errorTail_ok ht'
  rfl

section Runs

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## The handling of an error -/

/-- `run_errorTail` of `LeanExe/A64/Proof/WasiClocks.lean` as two cases: the handling of a result
in X0 that is no count, from `a`, with the return address in X19, returns its errno when the
negation of the result is at most 4095 and reaches the trap stub `tr` otherwise.  X0, X12, and X30
change, and the memory, SP, and the UART's state keep their values. -/
theorem run_errnoTail {a tr en : UInt64} {is : List Instr} (hg : errorTail a tr en = .ok is)
    (hcode : CodeAt code a is) (hen : CodeAt code en errnoRoutine) {s : State}
    (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 12 → q ≠ 30 → t.x q = s.x q) ∧
      ((0 - s.x 0 ≤ 4095 ∧ t.pc = s.x 19 ∧ t.x 0 = errnoLookup errnoTable (0 - s.x 0)) ∨
        (4095 < 0 - s.x 0 ∧ t.pc = tr)) := by
  obtain ⟨g1, g2, h1, h2, rfl⟩ := errorTail_ok hg
  obtain ⟨t, r, sp, m, io, k, hc⟩ := run_errorTail P code hcode h1 h2 hen hpc
  refine ⟨t, r, sp, m, io, k, ?_⟩
  by_cases h : 0 - s.x 0 ≤ 4095
  · rw [ite_eq_left h] at hc
    exact .inl ⟨h, hc⟩
  · rw [ite_eq_right h] at hc
    exact .inr ⟨UInt64.not_le.mp h, hc⟩

/-! ## A word stored at a guest address -/

/-- The four bytes of the low 32 bits of X0 stored at the guest's address `X17 + 4096 + Xp`, from
`a`: X12 and X16 change, and SP and the UART's state keep their values. -/
theorem run_wordStore {a : UInt64} {p : Fin 32} (hcode : CodeAt code a (wordStore p)) {s : State}
    (hpc : s.pc = a)
    (hmap : ∀ k < 4, P.normal (s.x 17 + UInt64.ofNat 4096 + s.x p + UInt64.ofNat k) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.pc = after a 9 ∧ t.sp = s.sp ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 12 → q ≠ 16 → t.x q = s.x q) ∧
      t.mem = writeList s.mem (s.x 17 + UInt64.ofNat 4096 + s.x p)
        [(s.x 0).toUInt8, (s.x 0 >>> UInt64.ofNat 8).toUInt8,
          (s.x 0 >>> UInt64.ofNat 16).toUInt8, (s.x 0 >>> UInt64.ofNat 24).toUInt8] := by
  have c0 := hcode 0 (by simp [wordStore, store32])
  have c1 := hcode 1 (by simp [wordStore, store32])
  simp only [wordStore, store32, List.cons_append, List.nil_append, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  have cstr : CodeAt code (after a 2) [.strb 0 16 4092, .lsrImm 12 0 8, .strb 12 16 4093,
      .lsrImm 12 0 16, .strb 12 16 4094, .lsrImm 12 0 24, .strb 12 16 4095] := by
    simpa [wordStore, store32] using CodeAt.drop_take code hcode 2 7 (by simp [wordStore, store32])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 16) (n := 17)
    (m := p) (by decide) (by rw [hpc]; exact c0)
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 16) (n := 16)
    (imm := 4) (by decide) (by decide) (by rw [p1, hpc, ← after_one]; exact c1)
  have e4 : (4 : Fin 4096).val = 4 := by decide
  rw [e4, x1] at x2
  have q2 : u2.pc = after a 2 := by
    rw [p2, p1, hpc, show a + 4 = after a 1 from (after_one a).symm, ← after_succ]
  have hB : ∀ k, u2.x 16 + UInt64.ofNat (4092 + k) =
      s.x 17 + UInt64.ofNat 4096 + s.x p + UInt64.ofNat k := by
    intro k
    rw [x2]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  obtain ⟨u3, r3, p3, sp3, io3, k3, m3⟩ := run_strb4 P code (v := 0) (t := 12) (s := u2)
    (by decide) (by decide) (by decide) cstr q2 (fun k hk => by rw [hB k]; exact hmap k hk) hU
  refine ⟨u3, r1.trans (r2.trans r3), by rw [p3, after_after], by rw [sp3, sp2, sp1],
    by rw [io3, io2, io1], fun q h12 h16 => by rw [k3 q h12, k2 q h16, k1 q h16], ?_⟩
  have hB0 : u2.x 16 + UInt64.ofNat 4092 = s.x 17 + UInt64.ofNat 4096 + s.x p := by
    have := hB 0
    simpa using this
  rw [m3, m2, m1, hB0, k2 0 (by decide), k1 0 (by decide)]

/-! ## The result of a read or a write on a handle -/

/-- The handling of the call's result in X0, from `a`, with the length in X11, the count's pointer
in X3, the return address in X19, the trap stub at `tr`, and the routine of errnos at `en`.  A
result at most the length is stored at the count's pointer and errno 0 returned.  When the negation
of a result above the length is at most 4095, it is an error number, whose errno is returned.  Any
other result reaches the trap stub.  X17, X18, SP, and the UART's state keep their values, and
only the store of a count changes the memory. -/
theorem run_countTail {a tr en : UInt64} {is : List Instr} (hg : countTail a tr en = .ok is)
    (hcode : CodeAt code a is) (hen : CodeAt code en errnoRoutine) {s : State} (hpc : s.pc = a)
    (hmap : s.x 0 ≤ s.x 11 →
      ∀ k < 4, P.normal (s.x 17 + UInt64.ofNat 4096 + s.x 3 + UInt64.ofNat k) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      ((s.x 0 ≤ s.x 11 ∧ t.pc = s.x 19 ∧ t.x 0 = 0 ∧
          t.mem = writeList s.mem (s.x 17 + UInt64.ofNat 4096 + s.x 3)
            [(s.x 0).toUInt8, (s.x 0 >>> UInt64.ofNat 8).toUInt8,
              (s.x 0 >>> UInt64.ofNat 16).toUInt8, (s.x 0 >>> UInt64.ofNat 24).toUInt8]) ∨
        (s.x 11 < s.x 0 ∧ 0 - s.x 0 ≤ 4095 ∧ t.pc = s.x 19 ∧
          t.x 0 = errnoLookup errnoTable (0 - s.x 0) ∧ t.mem = s.mem) ∨
        (s.x 11 < s.x 0 ∧ 4095 < 0 - s.x 0 ∧ t.pc = tr ∧ t.mem = s.mem)) := by
  obtain ⟨g1, tail, hg1, ht, rfl⟩ := countTail_ok hg
  have hl : (wordStore 3).length = 9 := rfl
  have cA := CodeAt.split code hcode (n := 13) (by simp [hl])
  have cB := CodeAt.split code cA.1 (n := 11) (by simp [hl])
  have cC := CodeAt.split code cB.1 (n := 2) rfl
  have c11 := cB.2 0 (by simp)
  have c12 := cB.2 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c11 c12
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiReg P code (x := 0) (y := 11)
    (tB := after a 13) cC.1 hg1 hpc
  by_cases hle : s.x 11 < s.x 0
  · rw [ite_eq_left hle] at p1
    obtain ⟨u2, r2, sp2, m2, io2, k2, hc⟩ := run_errnoTail P code ht cA.2 hen p1
    have hk : ∀ q : Fin 32, q ≠ 0 → q ≠ 12 → q ≠ 30 → u2.x q = s.x q :=
      fun q h0 h12 h30 => by rw [k2 q h0 h12 h30, k1]
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      hk 17 (by decide) (by decide) (by decide), hk 18 (by decide) (by decide) (by decide), ?_⟩
    simp only [k1] at hc
    rcases hc with ⟨h4095, p2, x2⟩ | ⟨hbig, p2⟩
    · exact .inr (.inl ⟨hle, h4095, p2, x2, by rw [m2, m1]⟩)
    · exact .inr (.inr ⟨hle, hbig, p2, by rw [m2, m1]⟩)
  · rw [ite_eq_right hle] at p1
    have hle' : s.x 0 ≤ s.x 11 := UInt64.not_lt.mp hle
    obtain ⟨u2, r2, p2, sp2, io2, k2, m2⟩ := run_wordStore P code (p := 3) (s := u1) cC.2 p1
      (fun k hk => by simp only [k1]; exact hmap hle' k hk) hU
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [p2, after_after]; exact c11)
    obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := step_ret P code (s := u3) (n := 19)
      (by rw [p3, p2, after_after, ← after_succ]; exact c12)
    have hk : ∀ q : Fin 32, q ≠ 0 → q ≠ 12 → q ≠ 16 → u4.x q = s.x q :=
      fun q h0 h12 h16 => by rw [k4, k3 q h0, k2 q h12 h16, k1]
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), by rw [sp4, sp3, sp2, sp1],
      by rw [io4, io3, io2, io1], hk 17 (by decide) (by decide) (by decide),
      hk 18 (by decide) (by decide) (by decide), .inl ⟨hle', ?_, ?_, ?_⟩⟩
    · rw [p4, k3 19 (by decide), k2 19 (by decide) (by decide), k1]
    · rw [k4, x3, movz0_val]
      decide
    · rw [m4, m3, m2, m1]
      simp only [k1]

/-! ## `fd_close` -/

/-- The stub of `fd_close` from its entry to the call: for a descriptor in X0 of at most 1,023
whose byte in the scratch, `sc` bytes above the area, is nonzero, the `BL` of the call, at
`after a 13`, with X0, X8 at 57, `close`, X20 at the scratch, X19 at the return address, and X21
at the descriptor.  For every other descriptor, the return to X30 with errno 8.  The memory, SP,
the UART's state, X17, and X18 keep their values. -/
theorem run_closeFront {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : closeStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = a)
    (hmap : s.x 0 ≤ 1023 → P.normal (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧
      t.x 18 = s.x 18 ∧
      if s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0 then
        t.pc = after a 13 ∧ t.x 0 = s.x 0 ∧ t.x 8 = 57 ∧ t.x 20 = s.x 17 + UInt64.ofNat sc ∧
          t.x 19 = s.x 30 ∧ t.x 21 = s.x 0 ∧ t.x 30 = s.x 30
      else t.pc = s.x 30 ∧ t.x 0 = 8 := by
  obtain ⟨held, tail, g13, g17, g19, hh, ht, h13, h17, h19, rfl⟩ := closeStub_ok hg
  obtain ⟨g1, g4, hg1, hg4, rfl⟩ := heldTest_ok hh
  obtain ⟨t2, t4, ht2, ht4, rfl⟩ := errorTail_ok ht
  have cS : CodeAt code a (scratchAddr sc) := by
    simpa [after_zero, scratchAddr, movImm] using CodeAt.drop_take code hcode 0 5
      (by simp [scratchAddr, movImm])
  have cH : CodeAt code (after a 5) [.subsImm 31 0 1023, .bcond 8 g1, .addReg 10 20 0,
      .ldrb 9 10 16, .cbz 9 g4] := by
    simpa [scratchAddr, movImm] using CodeAt.drop_take code hcode 5 5 (by simp [scratchAddr,
      movImm])
  have c10 := hcode 10 (by simp [scratchAddr, movImm])
  have c11 := hcode 11 (by simp [scratchAddr, movImm])
  have c12 := hcode 12 (by simp [scratchAddr, movImm])
  simp only [scratchAddr, movImm, List.cons_append, List.nil_append, List.getElem_cons_zero,
    List.getElem_cons_succ] at c10 c11 c12
  have cE : CodeAt code (after a 28) [.movz 0 8 0, .ret 30] := by
    simpa [scratchAddr, movImm] using CodeAt.drop_take code hcode 28 2 (by simp [scratchAddr,
      movImm])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_scratchAddr P code cS hpc
  have k10 : u1.x 0 = s.x 0 := k1 0 (by decide)
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_heldTest P code (r := 0) (by decide) cH
    hg1 hg4 p1
    (fun h => by rw [x1, k10]; exact hmap (by rwa [k10] at h))
  rw [x1, k10, m1] at p2
  simp only [after_after] at p2
  have kk2 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 20 → u2.x q = s.x q :=
    fun q h9 h10 h16 => by rw [k2 q h9 h10, k1 q h16]
  by_cases hheld : s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0
  · rw [ite_eq_left hheld] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_mov P code (s := u2) (d := 19) (m := 30)
      (by decide) (by rw [p2]; exact c10)
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_mov P code (s := u3) (d := 21) (m := 0)
      (by decide) (by rw [p3, p2, ← after_succ]; exact c11)
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_movz P code (s := u4) (d := 8) (imm := 57)
      (hw := 0) (by decide) (by rw [p4, p3, p2, ← after_succ, ← after_succ]; exact c12)
    have kk : ∀ q : Fin 32, q ≠ 8 → q ≠ 9 → q ≠ 10 → q ≠ 20 → q ≠ 19 → q ≠ 21 →
        u5.x q = s.x q := fun q h8 h9 h10 h16 h19 h21 => by
      rw [k5 q h8, k4 q h21, k3 q h19, kk2 q h9 h10 h16]
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))),
      by rw [sp5, sp4, sp3, sp2, sp1], by rw [m5, m4, m3, m2, m1],
      by rw [io5, io4, io3, io2, io1],
      kk 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      kk 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩
    rw [ite_eq_left hheld]
    refine ⟨by rw [p5, p4, p3, p2, ← after_succ, ← after_succ, ← after_succ],
      kk 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      by rw [x5, movz0_val]; rfl, ?_, ?_, ?_,
      kk 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
    · rw [k5 20 (by decide), k4 20 (by decide), k3 20 (by decide), k2 20 (by decide)
        (by decide), x1]
    · rw [k5 19 (by decide), k4 19 (by decide), x3, kk2 30 (by decide) (by decide) (by decide)]
    · rw [k5 21 (by decide), x4, k3 0 (by decide), kk2 0 (by decide) (by decide) (by decide)]
  · rw [ite_eq_right hheld] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_movzRet P code cE p2
    refine ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [m3, m2, m1],
      by rw [io3, io2, io1], by rw [k3 17 (by decide), kk2 17 (by decide) (by decide) (by decide)],
      by rw [k3 18 (by decide), kk2 18 (by decide) (by decide) (by decide)], ?_⟩
    rw [ite_eq_right hheld]
    exact ⟨by rw [p3, kk2 30 (by decide) (by decide) (by decide)], by rw [x3]; rfl⟩

/-- The stub of `fd_close` from the call's result in X0, at `after a 14`, with the scratch's
address in X20, the descriptor in X21, and the return address in X19: the descriptor's byte and,
for descriptor 3, the preopen flag cleared, and then the return of errno 0 for a result of 0, the
return of the errno of a negated error number, or the trap stub `tr`.  SP, the UART's state, X17,
and X18 keep their values. -/
theorem run_closeBack {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : closeStub a svc tr en sc = .ok is) (hcode : CodeAt code a is)
    (hen : CodeAt code en errnoRoutine) {s : State} (hpc : s.pc = after a 14)
    (hbyte : P.normal (s.x 20 + s.x 21 + 16) = true) (hflag : P.normal (s.x 20 + 8) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      t.mem = (if s.x 21 = 3 then store8 (store8 s.mem (s.x 20 + s.x 21 + 16) 0) (s.x 20 + 8) 0
        else store8 s.mem (s.x 20 + s.x 21 + 16) 0) ∧
      ((s.x 0 = 0 ∧ t.pc = s.x 19 ∧ t.x 0 = 0) ∨
        (s.x 0 ≠ 0 ∧ 0 - s.x 0 ≤ 4095 ∧ t.pc = s.x 19 ∧
          t.x 0 = errnoLookup errnoTable (0 - s.x 0)) ∨
        (s.x 0 ≠ 0 ∧ 4095 < 0 - s.x 0 ∧ t.pc = tr)) := by
  obtain ⟨held, tail, g13, g17, g19, hh, ht, h13, h17, h19, rfl⟩ := closeStub_ok hg
  obtain ⟨g1, g4, hg1, hg4, rfl⟩ := heldTest_ok hh
  obtain ⟨t2, t4, ht2, ht4, rfl⟩ := errorTail_ok ht
  have c14 := hcode 14 (by simp [scratchAddr, movImm])
  have c15 := hcode 15 (by simp [scratchAddr, movImm])
  have c18 := hcode 18 (by simp [scratchAddr, movImm])
  have c19 := hcode 19 (by simp [scratchAddr, movImm])
  simp only [scratchAddr, movImm, List.cons_append, List.nil_append, List.getElem_cons_zero,
    List.getElem_cons_succ] at c14 c15 c18 c19
  have c1617 : CodeAt code (after a 16) [.subsImm 31 21 3, .bcond 1 g17] := by
    simpa [scratchAddr, movImm] using CodeAt.drop_take code hcode 16 2 (by simp [scratchAddr,
      movImm])
  have cT : CodeAt code (after a 20) [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 t2,
      .orrReg 0 31 12, .bl t4, .ret 19] := by
    simpa [scratchAddr, movImm] using CodeAt.drop_take code hcode 20 6 (by simp [scratchAddr,
      movImm])
  have cOk : CodeAt code (after a 26) [.movz 0 0 0, .ret 19] := by
    simpa [scratchAddr, movImm] using CodeAt.drop_take code hcode 26 2 (by simp [scratchAddr,
      movImm])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 10) (n := 20)
    (m := 21) (by decide) (by rw [hpc]; exact c14)
  obtain ⟨u2, r2, p2, k2, sp2, io2, m2⟩ := step_strb P code (s := u1) (t := 31) (n := 10)
    (imm := 16) (k := 16) (addr := s.x 20 + s.x 21 + 16) (by decide)
    (by rw [p1, hpc, ← after_succ]; exact c15) rfl (by rw [x1]; rfl) hbyte hU
  have q2 : u2.pc = after a 16 := by rw [p2, p1, hpc, ← after_succ, ← after_succ]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_neImm P code (r := 21) (imm := 3)
    (tB := after a 19) (by decide) c1617 (by rw [after_after]; exact cbField_target h17) q2
  rw [show UInt64.ofNat (3 : Fin 4096).val = 3 from rfl, k2, k1 21 (by decide),
    after_after] at p3
  have hm2 : u2.mem = store8 s.mem (s.x 20 + s.x 21 + 16) 0 := by
    rw [m2, m1]
    rfl
  have kk3 : ∀ q : Fin 32, q ≠ 10 → u3.x q = s.x q := fun q h10 => by rw [k3, k2, k1 q h10]
  -- the preopen flag, cleared for descriptor 3
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ : ∃ u4, Reach P code u3 u4 ∧ u4.pc = after a 19 ∧
      (∀ q : Fin 32, u4.x q = u3.x q) ∧ u4.sp = u3.sp ∧
      u4.mem = (if s.x 21 = 3 then store8 (store8 s.mem (s.x 20 + s.x 21 + 16) 0) (s.x 20 + 8) 0
        else store8 s.mem (s.x 20 + s.x 21 + 16) 0) ∧ u4.io = u3.io := by
    by_cases h3 : s.x 21 = 3
    · rw [ite_eq_left h3] at p3
      obtain ⟨u4, r4, p4, k4, sp4, io4, m4⟩ := step_strb P code (s := u3) (t := 31) (n := 20)
        (imm := 8) (k := 8) (addr := s.x 20 + 8) (by decide) (by rw [p3]; exact c18) rfl
        (by rw [kk3 20 (by decide)]; rfl) hflag hU
      refine ⟨u4, r4, by rw [p4, p3, ← after_succ], k4, sp4, ?_, io4⟩
      rw [ite_eq_left h3, m4, m3, hm2]
      rfl
    · rw [ite_eq_right h3] at p3
      exact ⟨u3, .refl _, p3, fun _ => rfl, rfl, by rw [ite_eq_right h3, m3, hm2], rfl⟩
  have kk4 : ∀ q : Fin 32, q ≠ 10 → u4.x q = s.x q := fun q h10 => by rw [k4, kk3 q h10]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbz P code (s := u4) (r := 0) (g := g19)
    (target := after a 26) (by rw [p4]; exact c19) (by rw [p4]; exact cbField_target h19)
  rw [kk4 0 (by decide), p4, ← after_succ] at p5
  have r15 : Reach P code s u5 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  have kk5 : ∀ q : Fin 32, q ≠ 10 → u5.x q = s.x q := fun q h10 => by rw [k5, kk4 q h10]
  have hsp5 : u5.sp = s.sp := by rw [sp5, sp4, sp3, sp2, sp1]
  have hio5 : u5.io = s.io := by rw [io5, io4, io3, io2, io1]
  by_cases h0 : s.x 0 = 0
  · rw [ite_eq_left h0] at p5
    obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_movz P code (s := u5) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [p5]; exact (CodeAt.cons.mp cOk).1)
    obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_ret P code (s := u6) (n := 19)
      (by rw [p6, p5, ← after_one]; exact (CodeAt.cons.mp (CodeAt.cons.mp cOk).2).1)
    refine ⟨u7, r15.trans (r6.trans r7), by rw [sp7, sp6, hsp5], by rw [io7, io6, hio5],
      by rw [k7, k6 17 (by decide), kk5 17 (by decide)],
      by rw [k7, k6 18 (by decide), kk5 18 (by decide)], by rw [m7, m6, m5, m4], .inl ⟨h0, ?_, ?_⟩⟩
    · rw [p7, k6 19 (by decide), kk5 19 (by decide)]
    · rw [k7, x6, movz0_val]
      rfl
  · rw [ite_eq_right h0] at p5
    obtain ⟨u6, r6, sp6, m6, io6, k6, hc⟩ := run_errnoTail P code ht cT hen p5
    rw [kk5 0 (by decide), kk5 19 (by decide)] at hc
    refine ⟨u6, r15.trans r6, by rw [sp6, hsp5], by rw [io6, hio5],
      by rw [k6 17 (by decide) (by decide) (by decide), kk5 17 (by decide)],
      by rw [k6 18 (by decide) (by decide) (by decide), kk5 18 (by decide)],
      by rw [m6, m5, m4], ?_⟩
    rcases hc with ⟨h4095, p6, x6⟩ | ⟨hbig, p6⟩
    · exact .inr (.inl ⟨h0, h4095, p6, x6⟩)
    · exact .inr (.inr ⟨h0, hbig, p6⟩)

/-! ## `fd_read` and `fd_write` on a handle -/

/-- The stub of `fd_read` or `fd_write` on a handle from its entry to the call.  With the memory's
size, 8 plus the area's first word, and the iovec's eight bytes `w` at the guest's address in X1,
whose low half is the buffer's pointer and whose high half its length: when the iovec count in X2
is 1 and the iovec, the buffer, and the count's four bytes at the guest's address in X3 lie within
the memory, the `BL` of the call, at `after a 39`, with X0 kept, X1 at the buffer's address, X2
and X11 at the length, X8 at the call's number `nr`, and X19 at the return address, for a
descriptor in X0 of at most 1,023 whose byte in the scratch, `sc` bytes above the area, is
nonzero, and the return to X30 with errno 8 for every other descriptor.  Otherwise the trap stub
`tr`.  The memory, SP, the UART's state, X3, X17, and X18 keep their values. -/
theorem run_handleFront {nr : Fin 65536} {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : handleStub nr a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = a) (hsize : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true)
    (helem : ¬ load64 s.mem (s.x 17) + 8 < s.x 1 + 8 →
      ∀ k < 8, P.normal (s.x 17 + s.x 1 + UInt64.ofNat (4096 + k)) = true)
    (hbyte : s.x 0 ≤ 1023 → P.normal (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧
      t.x 18 = s.x 18 ∧
      if s.x 2 = 1 ∧ ¬ load64 s.mem (s.x 17) + 8 < s.x 1 + 8 ∧
          ¬ load64 s.mem (s.x 17) + 8 <
            (load64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat 4096)).toUInt32.toUInt64 +
              load64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat 4096) >>> UInt64.ofNat 32 ∧
          ¬ load64 s.mem (s.x 17) + 8 < s.x 3 + 4 then
        if s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0 then
          t.pc = after a 39 ∧ t.x 0 = s.x 0 ∧
            t.x 1 = s.x 17 + UInt64.ofNat 4096 +
              (load64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat 4096)).toUInt32.toUInt64 ∧
            t.x 2 = load64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat 4096) >>> UInt64.ofNat 32 ∧
            t.x 3 = s.x 3 ∧ t.x 8 = UInt64.ofNat nr.val ∧
            t.x 11 = load64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat 4096) >>> UInt64.ofNat 32 ∧
            t.x 19 = s.x 30 ∧ t.x 30 = s.x 30
        else t.pc = s.x 30 ∧ t.x 0 = 8
      else t.pc = tr := by
  obtain ⟨r1, r2, r3, held, tail, g1, g39, h1, h2, h3, hh, ht, hg1, hg39, rfl⟩ :=
    handleStub_ok hg
  obtain ⟨f1, hf1, rfl⟩ := rangeCheck_ok h1
  obtain ⟨f2, hf2, rfl⟩ := rangeCheck_ok h2
  obtain ⟨f3, hf3, rfl⟩ := rangeCheck_ok h3
  obtain ⟨e1, e4, he1, he4, rfl⟩ := heldTest_ok hh
  obtain ⟨d1, tail', hd1, ht', rfl⟩ := countTail_ok ht
  obtain ⟨t2, t4, ht2, ht4, rfl⟩ := errorTail_ok ht'
  have c01 : CodeAt code a [.subsImm 31 2 1, .bcond 1 g1] := by
    simpa [after_zero, scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 0 2 (by simp [scratchAddr, movImm, wordStore, store32])
  have cR1 : CodeAt code (after a 3)
      [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 f1] := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 3 4 (by simp [scratchAddr, movImm, wordStore, store32])
  have cR2 : CodeAt code (after a 12)
      [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 f2] := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 12 4 (by simp [scratchAddr, movImm, wordStore, store32])
  have cR3 : CodeAt code (after a 17)
      [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 f3] := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 17 4 (by simp [scratchAddr, movImm, wordStore, store32])
  have cS : CodeAt code (after a 21) (scratchAddr sc) := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 21 5 (by simp [scratchAddr, movImm, wordStore, store32])
  have cH : CodeAt code (after a 26)
      [.subsImm 31 0 1023, .bcond 8 e1, .addReg 10 20 0, .ldrb 9 10 16, .cbz 9 e4] := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 26 5 (by simp [scratchAddr, movImm, wordStore, store32])
  have cC : CodeAt code (after a 33) [.addReg 1 17 10, .addImm 1 1 4095, .addImm 1 1 1,
      .orrReg 2 31 11, .movz 8 nr 0, .orrReg 19 31 30, .bl g39] := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 33 7 (by simp [scratchAddr, movImm, wordStore, store32])
  have cE : CodeAt code (after a 59) [.movz 0 8 0, .ret 30] := by
    simpa [scratchAddr, movImm, wordStore, store32] using
      CodeAt.drop_take code hcode 59 2 (by simp [scratchAddr, movImm, wordStore, store32])
  have c2 := hcode 2 (by simp [scratchAddr, movImm, wordStore, store32])
  have c7 := hcode 7 (by simp [scratchAddr, movImm, wordStore, store32])
  have c8 := hcode 8 (by simp [scratchAddr, movImm, wordStore, store32])
  have c9 := hcode 9 (by simp [scratchAddr, movImm, wordStore, store32])
  have c10 := hcode 10 (by simp [scratchAddr, movImm, wordStore, store32])
  have c11 := hcode 11 (by simp [scratchAddr, movImm, wordStore, store32])
  have c16 := hcode 16 (by simp [scratchAddr, movImm, wordStore, store32])
  have c31 := hcode 31 (by simp [scratchAddr, movImm, wordStore, store32])
  have c32 := hcode 32 (by simp [scratchAddr, movImm, wordStore, store32])
  simp only [scratchAddr, movImm, wordStore, store32, List.cons_append, List.nil_append,
    List.getElem_cons_zero, List.getElem_cons_succ] at c2 c7 c8 c9 c10 c11 c16 c31 c32
  -- the iovec count
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_neImm P code (r := 2) (imm := 1) (tB := tr)
    (by decide) c01 (cbField_target hg1) hpc
  rw [show UInt64.ofNat (1 : Fin 4096).val = 1 from rfl] at p1
  by_cases hc1 : s.x 2 = 1
  swap
  · rw [ite_eq_right hc1] at p1
    refine ⟨u1, r1, sp1, m1, io1, k1 17, k1 18, ?_⟩
    rw [ite_eq_right (fun h => hc1 h.1)]
    exact p1
  rw [ite_eq_left hc1] at p1
  -- the iovec's range
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 12) (n := 1)
    (imm := 8) (by decide) (by decide) (by rw [p1]; exact c2)
  rw [show UInt64.ofNat (8 : Fin 4096).val = 8 from rfl, k1] at x2
  have k21 : ∀ q : Fin 32, q ≠ 12 → u2.x q = s.x q := fun q h => by rw [k2 q h, k1]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_rangeCheck P code cR1
    hf1 (s := u2) (by rw [p2, p1, ← after_succ])
    (fun k hk => by rw [k21 17 (by decide)]; exact hsize k hk)
  rw [m2, m1, k21 17 (by decide), x2, after_after] at p3
  by_cases hc2 : load64 s.mem (s.x 17) + 8 < s.x 1 + 8
  · rw [ite_eq_left hc2] at p3
    refine ⟨u3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [m3, m2, m1],
      by rw [io3, io2, io1], by rw [k3 17 (by decide), k21 17 (by decide)],
      by rw [k3 18 (by decide), k21 18 (by decide)], ?_⟩
    rw [ite_eq_right (fun h => h.2.1 hc2)]
    exact p3
  rw [ite_eq_right hc2] at p3
  have k31 : ∀ q : Fin 32, q ≠ 12 → q ≠ 13 → u3.x q = s.x q := fun q h12 h13 => by
    rw [k3 q h13, k21 q h12]
  have m31 : u3.mem = s.mem := by rw [m3, m2, m1]
  -- the iovec's eight bytes
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addReg P code (s := u3) (d := 14) (n := 17)
    (m := 1) (by decide) (by rw [p3]; exact c7)
  rw [k31 17 (by decide) (by decide), k31 1 (by decide) (by decide)] at x4
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_ldr P code (s := u4) (t := 14) (n := 14)
    (i := 512) (by decide) (by decide) (by decide) (by rw [p4, p3, ← after_succ]; exact c8)
    (fun k hk => by rw [x4]; exact helem hc2 k hk)
  rw [m4, m31, x4, show (8 * 512 : Nat) = 4096 from rfl] at x5
  generalize hw : load64 s.mem (s.x 17 + s.x 1 + UInt64.ofNat 4096) = w at x5 ⊢
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_orrW P code (s := u5) (d := 9) (n := 14)
    (by decide) (by rw [p5, p4, p3, ← after_succ, ← after_succ]; exact c9)
  have q6 : u6.pc = after a 10 := by
    rw [p6, p5, p4, p3, ← after_succ, ← after_succ, ← after_succ]
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_lsrImm P code (s := u6) (d := 12) (n := 14)
    (k := 32) (by decide) (by rw [q6]; exact c10) rfl
  have q7 : u7.pc = after a 11 := by rw [p7, q6, ← after_succ]
  obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := step_addReg P code (s := u7) (d := 12) (n := 9)
    (m := 12) (by decide) (by rw [q7]; exact c11)
  have hx12 : u8.x 12 = w.toUInt32.toUInt64 + w >>> UInt64.ofNat 32 := by
    rw [x8, k7 9 (by decide), x6, x7, k6 14 (by decide), x5]
  have k81 : ∀ q : Fin 32, q ≠ 9 → q ≠ 12 → q ≠ 13 → q ≠ 14 → u8.x q = s.x q :=
    fun q h9 h12 h13 h14 => by
      rw [k8 q h12, k7 q h12, k6 q h9, k5 q h14, k4 q h14, k31 q h12 h13]
  have hx14 : u8.x 14 = w := by
    rw [k8 14 (by decide), k7 14 (by decide), k6 14 (by decide), x5]
  have m81 : u8.mem = s.mem := by rw [m8, m7, m6, m5, m4, m31]
  have r18 : Reach P code s u8 :=
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans r8))))))
  have q8 : u8.pc = after a 12 := by rw [p8, q7, ← after_succ]
  -- the buffer's range
  obtain ⟨u9, r9, p9, k9, sp9, m9, io9⟩ := run_rangeCheck P code cR2
    hf2 (s := u8) q8
    (fun k hk => by rw [k81 17 (by decide) (by decide) (by decide) (by decide)]; exact hsize k hk)
  rw [m81, k81 17 (by decide) (by decide) (by decide) (by decide), hx12, after_after] at p9
  by_cases hc3 : load64 s.mem (s.x 17) + 8 < w.toUInt32.toUInt64 + w >>> UInt64.ofNat 32
  · rw [ite_eq_left hc3] at p9
    refine ⟨u9, r18.trans r9, by rw [sp9, sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1],
      by rw [m9, m81], by rw [io9, io8, io7, io6, io5, io4, io3, io2, io1],
      by rw [k9 17 (by decide), k81 17 (by decide) (by decide) (by decide) (by decide)],
      by rw [k9 18 (by decide), k81 18 (by decide) (by decide) (by decide) (by decide)], ?_⟩
    rw [ite_eq_right (fun h => h.2.2.1 hc3)]
    exact p9
  rw [ite_eq_right hc3] at p9
  -- the count's range
  have c16' : code u9.pc = some (encode (.addImm 12 3 4)) := by rw [p9]; exact c16
  obtain ⟨u10, r10, p10, x10, k10, sp10, m10, io10⟩ := step_addImm P code (s := u9) (d := 12)
    (n := 3) (imm := 4) (by decide) (by decide) c16'
  rw [show UInt64.ofNat (4 : Fin 4096).val = 4 from rfl, k9 3 (by decide),
    k81 3 (by decide) (by decide) (by decide) (by decide)] at x10
  obtain ⟨u11, r11, p11, k11, sp11, m11, io11⟩ := run_rangeCheck P code cR3
    hf3 (s := u10) (by rw [p10, p9, ← after_succ])
    (fun k hk => by
      rw [k10 17 (by decide), k9 17 (by decide),
        k81 17 (by decide) (by decide) (by decide) (by decide)]
      exact hsize k hk)
  rw [m10, m9, m81, k10 17 (by decide), k9 17 (by decide),
    k81 17 (by decide) (by decide) (by decide) (by decide), x10, after_after] at p11
  have k111 : ∀ q : Fin 32, q ≠ 9 → q ≠ 12 → q ≠ 13 → q ≠ 14 → u11.x q = s.x q :=
    fun q h9 h12 h13 h14 => by rw [k11 q h13, k10 q h12, k9 q h13, k81 q h9 h12 h13 h14]
  have hx14' : u11.x 14 = w := by
    rw [k11 14 (by decide), k10 14 (by decide), k9 14 (by decide), hx14]
  have r111 : Reach P code s u11 := r18.trans (r9.trans (r10.trans r11))
  have m111 : u11.mem = s.mem := by rw [m11, m10, m9, m81]
  have sp111 : u11.sp = s.sp := by rw [sp11, sp10, sp9, sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]
  have io111 : u11.io = s.io := by rw [io11, io10, io9, io8, io7, io6, io5, io4, io3, io2, io1]
  by_cases hc4 : load64 s.mem (s.x 17) + 8 < s.x 3 + 4
  · rw [ite_eq_left hc4] at p11
    refine ⟨u11, r111, sp111, m111, io111,
      k111 17 (by decide) (by decide) (by decide) (by decide),
      k111 18 (by decide) (by decide) (by decide) (by decide), ?_⟩
    rw [ite_eq_right (fun h => h.2.2.2 hc4)]
    exact p11
  rw [ite_eq_right hc4] at p11
  have hok : s.x 2 = 1 ∧ ¬ load64 s.mem (s.x 17) + 8 < s.x 1 + 8 ∧
      ¬ load64 s.mem (s.x 17) + 8 < w.toUInt32.toUInt64 + w >>> UInt64.ofNat 32 ∧
      ¬ load64 s.mem (s.x 17) + 8 < s.x 3 + 4 := ⟨hc1, hc2, hc3, hc4⟩
  -- the scratch and the held test
  obtain ⟨u12, r12, p12, x12, k12, sp12, m12, io12⟩ := run_scratchAddr P code cS (s := u11) p11
  rw [k111 17 (by decide) (by decide) (by decide) (by decide)] at x12
  have k120 : u12.x 0 = s.x 0 := by
    rw [k12 0 (by decide), k111 0 (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨u13, r13, p13, k13, sp13, m13, io13⟩ := run_heldTest P code (r := 0) (by decide) cH
    he1 he4 (s := u12)
    (by rw [p12, after_after])
    (fun h => by rw [x12, k120]; exact hbyte (by rwa [k120] at h))
  rw [x12, k120, m12, m111, after_after] at p13
  have k131 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 14 → q ≠ 20 →
      u13.x q = s.x q := fun q h9 h10 h12 h13 h14 h16 => by
    rw [k13 q h9 h10, k12 q h16, k111 q h9 h12 h13 h14]
  have r113 : Reach P code s u13 := r111.trans (r12.trans r13)
  have m113 : u13.mem = s.mem := by rw [m13, m12, m111]
  have sp113 : u13.sp = s.sp := by rw [sp13, sp12, sp111]
  have io113 : u13.io = s.io := by rw [io13, io12, io111]
  by_cases hheld : s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0
  · rw [ite_eq_left hheld] at p13
    obtain ⟨u14, r14, p14, x14, k14, sp14, m14, io14⟩ := step_orrW P code (s := u13) (d := 10)
      (n := 14) (by decide) (by rw [p13]; exact c31)
    obtain ⟨u15, r15, p15, x15, k15, sp15, m15, io15⟩ := step_lsrImm P code (s := u14) (d := 11)
      (n := 14) (k := 32) (by decide) (by rw [p14, p13, ← after_succ]; exact c32) rfl
    obtain ⟨u16, r16, p16, x16', x16, x18', x19, k16, sp16, m16, io16⟩ :=
      run_bufferCall P code cC (s := u15) (by rw [p15, p14, p13, ← after_succ, ← after_succ])
    have hx14'' : u13.x 14 = w := by
      rw [k13 14 (by decide) (by decide), k12 14 (by decide), hx14']
    refine ⟨u16, r113.trans (r14.trans (r15.trans r16)), by rw [sp16, sp15, sp14, sp113],
      by rw [m16, m15, m14, m113], by rw [io16, io15, io14, io113], ?_, ?_, ?_⟩
    · rw [k16 17 (by decide) (by decide) (by decide) (by decide), k15 17 (by decide),
        k14 17 (by decide), k131 17 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
    · rw [k16 18 (by decide) (by decide) (by decide) (by decide), k15 18 (by decide),
        k14 18 (by decide), k131 18 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
    rw [ite_eq_left hok, ite_eq_left hheld]
    refine ⟨by rw [p16, after_after], ?_, ?_, ?_, ?_, x18', ?_, ?_, ?_⟩
    · rw [k16 0 (by decide) (by decide) (by decide) (by decide), k15 0 (by decide),
        k14 0 (by decide), k131 0 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
    · rw [x16', k15 17 (by decide), k14 17 (by decide), k15 10 (by decide), x14, hx14'',
        k131 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [x16, x15, k14 14 (by decide), hx14'']
    · rw [k16 3 (by decide) (by decide) (by decide) (by decide), k15 3 (by decide),
        k14 3 (by decide), k131 3 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
    · rw [k16 11 (by decide) (by decide) (by decide) (by decide), x15, k14 14 (by decide),
        hx14'']
    · rw [x19, k15 30 (by decide), k14 30 (by decide), k131 30 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
    · rw [k16 30 (by decide) (by decide) (by decide) (by decide), k15 30 (by decide),
        k14 30 (by decide), k131 30 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
  · rw [ite_eq_right hheld] at p13
    obtain ⟨u14, r14, p14, x14, k14, sp14, m14, io14⟩ := run_movzRet P code cE (s := u13) p13
    refine ⟨u14, r113.trans r14, by rw [sp14, sp113], by rw [m14, m113], by rw [io14, io113],
      by rw [k14 17 (by decide), k131 17 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)],
      by rw [k14 18 (by decide), k131 18 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)], ?_⟩
    rw [ite_eq_left hok, ite_eq_right hheld]
    exact ⟨by rw [p14, k131 30 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)], by rw [x14]; rfl⟩

/-! ## The calls of `path_open` and their result -/

theorem openCalls_ok {a svc : UInt64} {is : List Instr} (hg : openCalls a svc = .ok is) :
    ∃ g7 g9 g11 g13, bField (after a 7) svc = .ok g7 ∧ cbField (after a 9) (after a 14) = .ok g9 ∧
      cbField (after a 11) (after a 14) = .ok g11 ∧ bField (after a 13) (after a 2) = .ok g13 ∧
      is = [.orrReg 22 31 0, .movz 23 0 0, .orrReg 0 31 22, .addImm 1 20 1080,
        .addImm 2 20 1056, .movz 3 24 0, .movz 8 437 0, .bl g7, .addImm 9 0 11, .cbnz 9 g9,
        .subsImm 31 23 2, .bcond 8 g11, .addImm 23 23 1, .b g13] := by
  unfold openCalls at hg
  cases h7 : bField (after a 7) svc with
  | error err => simp [h7, bind, Except.bind] at hg
  | ok g7 =>
  cases h9 : cbField (after a 9) (after a 14) with
  | error err => simp [h7, h9, bind, Except.bind] at hg
  | ok g9 =>
  cases h11 : cbField (after a 11) (after a 14) with
  | error err => simp [h7, h9, h11, bind, Except.bind] at hg
  | ok g11 =>
  cases h13 : bField (after a 13) (after a 2) with
  | error err => simp [h7, h9, h11, h13, bind, Except.bind] at hg
  | ok g13 =>
  simp only [h7, h9, h11, h13, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g7, g9, g11, g13, rfl, rfl, rfl, rfl, hg.symm⟩

theorem openResult_ok {a tr en : UInt64} {is : List Instr} (hg : openResult a tr en = .ok is) :
    ∃ g1 tail, cbField (after a 1) (after a 16) = .ok g1 ∧
      errorTail (after a 16) tr en = .ok tail ∧
      is = [.subsImm 31 0 1023, .bcond 8 g1, .addReg 10 20 0, .movz 9 1 0, .strb 9 10 16] ++
        wordStore 21 ++ [.movz 0 0 0, .ret 19] ++ tail := by
  unfold openResult at hg
  cases ht : errorTail (after a 16) tr en with
  | error err => simp [ht, bind, Except.bind] at hg
  | ok tail =>
  cases h1 : cbField (after a 1) (after a 16) with
  | error err => simp [ht, h1, bind, Except.bind] at hg
  | ok g1 =>
  simp only [ht, h1, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, tail, rfl, rfl, hg.symm⟩

/-- The setup of the `openat2` calls, from the start of `openCalls` at `a`: X22 at the directory
in X0 and X23 at 0. -/
theorem run_openStart {a svc : UInt64} {is : List Instr} (hg : openCalls a svc = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = after a 2 ∧ t.x 22 = s.x 0 ∧ t.x 23 = 0 ∧
      (∀ q : Fin 32, q ≠ 22 → q ≠ 23 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  obtain ⟨g7, g9, g11, g13, -, -, -, -, rfl⟩ := openCalls_ok hg
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 22) (m := 0)
    (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_movz P code (s := u1) (d := 23) (imm := 0)
    (hw := 0) (by decide) (by rw [q1]; exact c1)
  refine ⟨u2, r1.trans r2, by rw [p2, q1, ← after_succ], ?_, ?_,
    fun q h22 h23 => by rw [k2 q h23, k1 q h22], by rw [sp2, sp1], by rw [m2, m1],
    by rw [io2, io1]⟩
  · rw [k2 22 (by decide), x1]
  · rw [x2, movz0_val]; rfl

/-- The arguments of an `openat2` call, from `after a 2` of `openCalls` at `a` to its `BL` at
`after a 7`: X0 at the directory in X22, X1 and X2 at the path buffer and the `open_how` record,
1,080 and 1,056 bytes above the scratch's address in X20, X3 at the record's size 24, and X8 at
437, `openat2`. -/
theorem run_openArgs {a svc : UInt64} {is : List Instr} (hg : openCalls a svc = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = after a 2) :
    ∃ t, Reach P code s t ∧ t.pc = after a 7 ∧ t.x 0 = s.x 22 ∧
      t.x 1 = s.x 20 + UInt64.ofNat 1080 ∧ t.x 2 = s.x 20 + UInt64.ofNat 1056 ∧ t.x 3 = 24 ∧
      t.x 8 = 437 ∧ (∀ q : Fin 32, q ≠ 0 → q ≠ 1 → q ≠ 2 → q ≠ 3 → q ≠ 8 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨g7, g9, g11, g13, -, -, -, -, rfl⟩ := openCalls_ok hg
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  have c4 := hcode 4 (by simp)
  have c5 := hcode 5 (by simp)
  have c6 := hcode 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c2 c3 c4 c5 c6
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_mov P code (s := s) (d := 0) (m := 22)
    (by decide) (by rw [hpc]; exact c2)
  have q1 : u1.pc = after a 3 := by rw [p1, hpc, ← after_succ]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 1) (n := 20)
    (imm := 1080) (by decide) (by decide) (by rw [q1]; exact c3)
  have q2 : u2.pc = after a 4 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addImm P code (s := u2) (d := 2) (n := 20)
    (imm := 1056) (by decide) (by decide) (by rw [q2]; exact c4)
  have q3 : u3.pc = after a 5 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_movz P code (s := u3) (d := 3) (imm := 24)
    (hw := 0) (by decide) (by rw [q3]; exact c5)
  have q4 : u4.pc = after a 6 := by rw [p4, q3, ← after_succ]
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_movz P code (s := u4) (d := 8) (imm := 437)
    (hw := 0) (by decide) (by rw [q4]; exact c6)
  refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), by rw [p5, q4, ← after_succ], ?_, ?_,
    ?_, ?_, ?_, fun q h0 h1 h2 h3 h8 => by rw [k5 q h8, k4 q h3, k3 q h2, k2 q h1, k1 q h0],
    by rw [sp5, sp4, sp3, sp2, sp1], by rw [m5, m4, m3, m2, m1], by rw [io5, io4, io3, io2, io1]⟩
  · rw [k5 0 (by decide), k4 0 (by decide), k3 0 (by decide), k2 0 (by decide), x1]
  · rw [k5 1 (by decide), k4 1 (by decide), k3 1 (by decide), x2, k1 20 (by decide)]; rfl
  · rw [k5 2 (by decide), k4 2 (by decide), x3, k2 20 (by decide), k1 20 (by decide)]; rfl
  · rw [k5 3 (by decide), x4, movz0_val]; rfl
  · rw [x5, movz0_val]; rfl

/-- The test after an `openat2` call, from `after a 8` of `openCalls` at `a`: a result of `-EAGAIN`
with at most 2 in X23 returns to the call's arguments at `after a 2` with X23 increased by one, and
any other result reaches `after a 14`.  X9 and X23 change. -/
theorem run_openRetry {a svc : UInt64} {is : List Instr} (hg : openCalls a svc = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = after a 8) :
    ∃ t, Reach P code s t ∧
      (if s.x 0 = 0 - 11 ∧ s.x 23 ≤ 2 then t.pc = after a 2 ∧ t.x 23 = s.x 23 + 1
        else t.pc = after a 14 ∧ t.x 23 = s.x 23) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 23 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  obtain ⟨g7, g9, g11, g13, -, hg9, hg11, hg13, rfl⟩ := openCalls_ok hg
  have c8 := hcode 8 (by simp)
  have c9 := hcode 9 (by simp)
  have c12 := hcode 12 (by simp)
  have c13 := hcode 13 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at c8 c9 c12 c13
  have c1011 : CodeAt code (after a 10) [.subsImm 31 23 2, .bcond 8 g11] := by
    simpa using CodeAt.drop_take code hcode 10 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addImm P code (s := s) (d := 9) (n := 0)
    (imm := 11) (by decide) (by decide) (by rw [hpc]; exact c8)
  have q1 : u1.pc = after a 9 := by rw [p1, hpc, ← after_succ]
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbnz P code (s := u1) (r := 9) (g := g9)
    (target := after a 14) (by rw [q1]; exact c9) (by rw [q1]; exact cbField_target hg9)
  have hx9 : u1.x 9 = s.x 0 + 11 := x1
  have eag : s.x 0 + 11 = 0 ↔ s.x 0 = 0 - 11 := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      rfl
  have hr12 : Reach P code s u2 := r1.trans r2
  have kk2 : ∀ q : Fin 32, q ≠ 9 → u2.x q = s.x q := fun q h9 => by rw [k2, k1 q h9]
  by_cases hag : s.x 0 = 0 - 11
  · have h9 : u1.x 9 = 0 := by rw [hx9]; exact eag.mpr hag
    rw [ite_eq_right (by rw [h9]; exact fun h => h rfl), q1, ← after_succ] at p2
    obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_hiImm P code (r := 23) (imm := 2)
      (tB := after a 14) (by decide) c1011 (by rw [after_after]; exact cbField_target hg11) p2
    rw [show UInt64.ofNat (2 : Fin 4096).val = 2 from rfl, kk2 23 (by decide), after_after] at p3
    by_cases hc : 2 < s.x 23
    · rw [ite_eq_left hc] at p3
      refine ⟨u3, hr12.trans r3, ?_, fun q h9 _ => by rw [k3, kk2 q h9], by rw [sp3, sp2, sp1],
        by rw [m3, m2, m1], by rw [io3, io2, io1]⟩
      rw [ite_eq_right (fun h => absurd h.2 (UInt64.not_le.mpr hc))]
      exact ⟨p3, by rw [k3, kk2 23 (by decide)]⟩
    · rw [ite_eq_right hc] at p3
      obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addImm P code (s := u3) (d := 23)
        (n := 23) (imm := 1) (by decide) (by decide) (by rw [p3]; exact c12)
      obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_b P code (s := u4) (target := after a 2)
        (by rw [p4, p3, ← after_succ]; exact c13)
        (by rw [p4, p3, ← after_succ]; exact bField_target hg13)
      refine ⟨u5, hr12.trans (r3.trans (r4.trans r5)), ?_,
        fun q h9 h23 => by rw [k5, k4 q h23, k3, kk2 q h9], by rw [sp5, sp4, sp3, sp2, sp1],
        by rw [m5, m4, m3, m2, m1], by rw [io5, io4, io3, io2, io1]⟩
      rw [ite_eq_left ⟨hag, UInt64.not_lt.mp hc⟩]
      exact ⟨p5, by rw [k5, x4, k3, kk2 23 (by decide)]; rfl⟩
  · have h9 : u1.x 9 ≠ 0 := by rw [hx9]; exact fun h => hag (eag.mp h)
    rw [ite_eq_left h9] at p2
    refine ⟨u2, hr12, ?_, fun q h9 _ => kk2 q h9, by rw [sp2, sp1], by rw [m2, m1],
      by rw [io2, io1]⟩
    rw [ite_eq_right (fun h => hag h.1)]
    exact ⟨p2, kk2 23 (by decide)⟩

/-- The handling of the last `openat2`'s result in X0, from `a`: a descriptor of at most 1,023 sets
its byte 16 bytes above the scratch's address in X20 to 1, is stored at the guest's address in X21,
and returns errno 0 to X19, a negated error number returns its errno, and any other result reaches
the trap stub `tr`.  SP, the UART's state, X17, and X18 keep their values. -/
theorem run_openResult {a tr en : UInt64} {is : List Instr} (hg : openResult a tr en = .ok is)
    (hcode : CodeAt code a is) (hen : CodeAt code en errnoRoutine) {s : State} (hpc : s.pc = a)
    (hbyte : s.x 0 ≤ 1023 → P.normal (s.x 20 + s.x 0 + 16) = true)
    (hmap : s.x 0 ≤ 1023 →
      ∀ k < 4, P.normal (s.x 17 + UInt64.ofNat 4096 + s.x 21 + UInt64.ofNat k) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      ((s.x 0 ≤ 1023 ∧ t.pc = s.x 19 ∧ t.x 0 = 0 ∧
          t.mem = writeList (store8 s.mem (s.x 20 + s.x 0 + 16) 1)
            (s.x 17 + UInt64.ofNat 4096 + s.x 21)
            [(s.x 0).toUInt8, (s.x 0 >>> UInt64.ofNat 8).toUInt8,
              (s.x 0 >>> UInt64.ofNat 16).toUInt8, (s.x 0 >>> UInt64.ofNat 24).toUInt8]) ∨
        (1023 < s.x 0 ∧ 0 - s.x 0 ≤ 4095 ∧ t.pc = s.x 19 ∧
          t.x 0 = errnoLookup errnoTable (0 - s.x 0) ∧ t.mem = s.mem) ∨
        (1023 < s.x 0 ∧ 4095 < 0 - s.x 0 ∧ t.pc = tr ∧ t.mem = s.mem)) := by
  obtain ⟨g1, tail, hg1, ht, rfl⟩ := openResult_ok hg
  have hl : (wordStore 21).length = 9 := rfl
  have cA := CodeAt.split code hcode (n := 16) (by simp [hl])
  have cB := CodeAt.split code cA.1 (n := 14) (by simp [hl])
  have cC := CodeAt.split code cB.1 (n := 5) rfl
  have c2 := cC.1 2 (by simp)
  have c3 := cC.1 3 (by simp)
  have c4 := cC.1 4 (by simp)
  have c14 := cB.2 0 (by simp)
  have c15 := cB.2 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c2 c3 c4 c14 c15
  have c01 : CodeAt code a [.subsImm 31 0 1023, .bcond 8 g1] := by
    simpa [after_zero] using CodeAt.drop_take code cC.1 0 2 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_hiImm P code (r := 0) (imm := 1023)
    (tB := after a 16) (by decide) c01 (cbField_target hg1) hpc
  rw [show UInt64.ofNat (1023 : Fin 4096).val = 1023 from rfl] at p1
  by_cases hbig : 1023 < s.x 0
  · rw [ite_eq_left hbig] at p1
    obtain ⟨u2, r2, sp2, m2, io2, k2, hc⟩ := run_errnoTail P code ht cA.2 hen p1
    simp only [k1] at hc
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      by rw [k2 17 (by decide) (by decide) (by decide), k1],
      by rw [k2 18 (by decide) (by decide) (by decide), k1], ?_⟩
    rcases hc with ⟨h4095, p2, x2⟩ | ⟨hbig', p2⟩
    · exact .inr (.inl ⟨hbig, h4095, p2, x2, by rw [m2, m1]⟩)
    · exact .inr (.inr ⟨hbig, hbig', p2, by rw [m2, m1]⟩)
  · rw [ite_eq_right hbig] at p1
    have hle : s.x 0 ≤ 1023 := UInt64.not_lt.mp hbig
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addReg P code (s := u1) (d := 10) (n := 20)
      (m := 0) (by decide) (by rw [p1]; exact c2)
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := 9) (imm := 1)
      (hw := 0) (by decide) (by rw [p2, p1, ← after_succ]; exact c3)
    obtain ⟨u4, r4, p4, k4, sp4, io4, m4⟩ := step_strb P code (s := u3) (t := 9) (n := 10)
      (imm := 16) (k := 16) (addr := s.x 20 + s.x 0 + 16) (by decide)
      (by rw [p3, p2, p1, ← after_succ, ← after_succ]; exact c4) rfl
      (by rw [k3 10 (by decide), x2, k1, k1]; rfl) (hbyte hle) hU
    have q4 : u4.pc = after a 5 := by rw [p4, p3, p2, p1, ← after_succ, ← after_succ, ← after_succ]
    have kk4 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → u4.x q = s.x q := fun q h9 h10 => by
      rw [k4, k3 q h9, k2 q h10, k1]
    obtain ⟨u5, r5, p5, sp5, io5, k5, m5⟩ := run_wordStore P code (p := 21) (s := u4) cC.2 q4
      (fun k hk => by
        rw [kk4 17 (by decide) (by decide), kk4 21 (by decide) (by decide)]
        exact hmap hle k hk) hU
    obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_movz P code (s := u5) (d := 0) (imm := 0)
      (hw := 0) (by decide) (by rw [p5, after_after]; exact c14)
    obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_ret P code (s := u6) (n := 19)
      (by rw [p6, p5, after_after, ← after_succ]; exact c15)
    have kk7 : ∀ q : Fin 32, q ≠ 0 → q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 16 → u7.x q = s.x q :=
      fun q h0 h9 h10 h12 h16 => by rw [k7, k6 q h0, k5 q h12 h16, kk4 q h9 h10]
    refine ⟨u7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))),
      by rw [sp7, sp6, sp5, sp4, sp3, sp2, sp1], by rw [io7, io6, io5, io4, io3, io2, io1],
      kk7 17 (by decide) (by decide) (by decide) (by decide) (by decide),
      kk7 18 (by decide) (by decide) (by decide) (by decide) (by decide),
      .inl ⟨hle, ?_, ?_, ?_⟩⟩
    · rw [p7, k6 19 (by decide), k5 19 (by decide) (by decide), kk4 19 (by decide) (by decide)]
    · rw [k7, x6, movz0_val]; rfl
    · have h91 : (u3.x 9).toUInt8 = 1 := by rw [x3, movz0_val]; rfl
      rw [m7, m6, m5, m4, m3, m2, m1, kk4 17 (by decide) (by decide),
        kk4 21 (by decide) (by decide), kk4 0 (by decide) (by decide), h91]

end Runs

end LeanExe.A64
