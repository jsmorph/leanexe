module

public import Verified.Shim
public import LeanExe.A64.Proof.WasiStubs
public import LeanExe.A64.Proof.WasiStrings
public import Verified.ShimA64.Clocks
public import LeanExe.A64.WasiFiles

@[expose] public section

/-!
The run of `openHow` of `LeanExe/A64/WasiFiles.lean` in the program's model.  `run_openHow`
follows the generator's words from the first to the word after them: they write the 24 bytes of
`openHowBytes arm64Flags`, the `open_how` record of the `openat2` call of `path_open`, 1,056 bytes
above the scratch's address in X20, and change no register but X9, X10, and X24 to X28.  The
proof splits the words at their forward branches: `run_openHowAccess` computes `O_CLOEXEC` and the
access mode, `run_openHowCreate` the creation flags and `O_DIRECTORY`, and `run_openHowTail`
`O_APPEND`, `O_NONBLOCK`, and `O_NOFOLLOW`, through runs such as `run_andCbzOrr` of a test
followed by an `ORR` into X24.  `openHow_flags` equates the word that they leave in X24 with
`openFlagsWord arm64Flags` by cases on the tested bits, and `store64_wasiBytes` gives the bytes
that each `STR` of a word writes.
-/

namespace Verified.ShimA64

open LeanExe LeanExe.A64 Verified.Shim

/-! ## Bytes of words -/

/-- Byte `k` of a word, below 8, in the machine's form and in the specification's form. -/
theorem byteOf_word (w : UInt64) {k : Nat} (hk : k < 8) :
    LeanExe.A64.byteOf w k = Verified.Wasi.byteOf w.toNat k := by
  apply UInt8.toNat_inj.mp
  rw [LeanExe.A64.byteOf_toNat w hk, Verified.Wasi.byteOf_toNat]

/-- A `store64` writes the word's eight little-endian bytes in the specification's form. -/
theorem store64_wasiBytes (m : UInt64 → UInt8) (a w : UInt64) :
    store64 m a w = writeList m a ((List.range 8).map (Verified.Wasi.byteOf w.toNat)) := by
  rw [store64_writeList]
  congr 1
  exact List.map_congr_left fun k hk => byteOf_word w (List.mem_range.mp hk)

/-- Three `store64` of consecutive words write their 24 little-endian bytes. -/
theorem store64_three (m : UInt64 → UInt8) (A w1 w2 w3 : UInt64) :
    store64 (store64 (store64 m A w1) (A + UInt64.ofNat 8) w2) (A + UInt64.ofNat 16) w3 =
      writeList m A ((List.range 8).map (Verified.Wasi.byteOf w1.toNat) ++
        (List.range 8).map (Verified.Wasi.byteOf w2.toNat) ++
        (List.range 8).map (Verified.Wasi.byteOf w3.toNat)) := by
  rw [writeList_append, writeList_append, ← store64_wasiBytes, ← store64_wasiBytes,
    ← store64_wasiBytes]
  simp only [List.length_append, List.length_map, List.length_range]

/-! ## The flags word -/

/-- The word that the code of `openHow` leaves in X24 is `openFlagsWord arm64Flags`. -/
theorem openHow_flags (dirflags oflags rights fdflags : UInt64) :
    0x80000 ||| (if rights &&& 64 ||| oflags &&& 1 ||| oflags &&& 8 = 0 then 0
        else if rights &&& 2 = 0 ∧ rights &&& 64 ≠ 0 then 1 else 2) |||
      (if oflags &&& 1 = 0 then 0 else 0x40) ||| (if oflags &&& 2 = 0 then 0 else 0x4000) |||
      (if (if oflags &&& 1 = 0 then 0 else oflags &&& 4) = 0 then 0 else 0x80) |||
      (if oflags &&& 8 = 0 then 0
        else if (if oflags &&& 1 = 0 then 0 else oflags &&& 4) = 0 then 0x200 else 0) |||
      (if fdflags &&& 1 = 0 then 0 else 0x400) ||| (if fdflags &&& 4 = 0 then 0 else 0x800) |||
      (if dirflags &&& 1 = 0 then 0x8000 else 0) =
      openFlagsWord arm64Flags dirflags oflags rights fdflags := by
  have hrw : (if rights &&& 64 ||| oflags &&& 1 ||| oflags &&& 8 = 0 then 0
        else if rights &&& 2 = 0 ∧ rights &&& 64 ≠ 0 then 1 else 2 : UInt64) =
      if (rights &&& 2 != 0 || rights &&& 64 == 0) &&
          (rights &&& 64 != 0 || oflags &&& 1 != 0 || oflags &&& 8 != 0) then 2
      else if rights &&& 64 != 0 || oflags &&& 1 != 0 || oflags &&& 8 != 0 then 1 else 0 := by
    by_cases a1 : oflags &&& 1 = 0 <;> by_cases a8 : oflags &&& 8 = 0 <;>
      by_cases b2 : rights &&& 2 = 0 <;> by_cases b64 : rights &&& 64 = 0 <;>
      simp [a1, a8, b2, b64]
  have hc : (if oflags &&& 1 = 0 then 0 else 0x40 : UInt64) =
      if oflags &&& 1 != 0 then 0x40 else 0 := by
    by_cases a1 : oflags &&& 1 = 0 <;> simp [a1]
  have hd : (if oflags &&& 2 = 0 then 0 else 0x4000 : UInt64) =
      if oflags &&& 2 != 0 then arm64Flags.directory else 0 := by
    by_cases a2 : oflags &&& 2 = 0 <;> simp [a2, arm64Flags]
  have he : (if (if oflags &&& 1 = 0 then 0 else oflags &&& 4) = 0 then 0 else 0x80 : UInt64) =
      if oflags &&& 1 != 0 && oflags &&& 4 != 0 then 0x80 else 0 := by
    by_cases a1 : oflags &&& 1 = 0 <;> by_cases a4 : oflags &&& 4 = 0 <;> simp [a1, a4]
  have ht : (if oflags &&& 8 = 0 then 0
        else if (if oflags &&& 1 = 0 then 0 else oflags &&& 4) = 0 then 0x200 else 0 : UInt64) =
      if oflags &&& 8 != 0 && !(oflags &&& 1 != 0 && oflags &&& 4 != 0) then 0x200 else 0 := by
    by_cases a1 : oflags &&& 1 = 0 <;> by_cases a4 : oflags &&& 4 = 0 <;>
      by_cases a8 : oflags &&& 8 = 0 <;> simp [a1, a4, a8]
  have ha : (if fdflags &&& 1 = 0 then 0 else 0x400 : UInt64) =
      if fdflags &&& 1 != 0 then 0x400 else 0 := by
    by_cases f1 : fdflags &&& 1 = 0 <;> simp [f1]
  have hn : (if fdflags &&& 4 = 0 then 0 else 0x800 : UInt64) =
      if fdflags &&& 4 != 0 then 0x800 else 0 := by
    by_cases f4 : fdflags &&& 4 = 0 <;> simp [f4]
  have hf : (if dirflags &&& 1 = 0 then 0x8000 else 0 : UInt64) =
      if dirflags &&& 1 == 0 then arm64Flags.nofollow else 0 := by
    by_cases d1 : dirflags &&& 1 = 0 <;> simp [d1, arm64Flags]
  rw [hrw, hc, hd, he, ht, ha, hn, hf]
  simp only [openFlagsWord]
  ac_rfl

/-! ## The generator's words -/

theorem openHow_ok {a : UInt64} {is : List Instr} (hg : openHow a = .ok is) :
    ∃ g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 : Fin 524288,
      cbField (after a 9) (after a 19) = .ok g1 ∧ cbField (after a 13) (after a 17) = .ok g2 ∧
      cbField (after a 16) (after a 18) = .ok g3 ∧ cbField (after a 19) (after a 22) = .ok g4 ∧
      cbField (after a 24) (after a 27) = .ok g5 ∧ cbField (after a 29) (after a 31) = .ok g6 ∧
      cbField (after a 31) (after a 34) = .ok g7 ∧ cbField (after a 34) (after a 38) = .ok g8 ∧
      cbField (after a 35) (after a 38) = .ok g9 ∧ cbField (after a 40) (after a 43) = .ok g10 ∧
      cbField (after a 45) (after a 48) = .ok g11 ∧ cbField (after a 50) (after a 53) = .ok g12 ∧
      cbField (after a 55) (after a 57) = .ok g13 ∧
      is = ([.movz 24 8 1, .movz 9 1 0, .andReg 25 4 9, .movz 9 8 0, .andReg 27 4 9,
          .movz 9 64 0, .andReg 28 5 9, .orrReg 28 28 25, .orrReg 28 28 27, .cbz 28 g1,
          .movz 9 1 0, .movz 10 2 0, .andReg 10 5 10, .cbnz 10 g2, .movz 10 64 0,
          .andReg 10 5 10, .cbnz 10 g3, .movz 9 2 0, .orrReg 24 24 9] : List Instr) ++
        ([.cbz 25 g4, .movz 9 0x40 0, .orrReg 24 24 9,
          .movz 9 2 0, .andReg 9 4 9, .cbz 9 g5, .movz 9 0x4000 0, .orrReg 24 24 9,
          .movz 9 4 0, .andReg 26 4 9, .cbnz 25 g6, .movz 26 0 0,
          .cbz 26 g7, .movz 9 0x80 0, .orrReg 24 24 9,
          .cbz 27 g8, .cbnz 26 g9, .movz 9 0x200 0, .orrReg 24 24 9] : List Instr) ++
        ([.movz 9 1 0, .andReg 9 7 9, .cbz 9 g10, .movz 9 0x400 0, .orrReg 24 24 9,
          .movz 9 4 0, .andReg 9 7 9, .cbz 9 g11, .movz 9 0x800 0, .orrReg 24 24 9,
          .movz 9 1 0, .andReg 9 1 9, .cbnz 9 g12, .movz 9 0x8000 0, .orrReg 24 24 9] :
          List Instr) ++
        ([.str 24 20 132, .movz 9 0 0, .cbz 25 g13, .movz 9 438 0, .str 9 20 133, .movz 9 10 0,
          .str 9 20 134] : List Instr) := by
  unfold openHow at hg
  cases h1 : cbField (after a 9) (after a 19) with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok g1 =>
  cases h2 : cbField (after a 13) (after a 17) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok g2 =>
  cases h3 : cbField (after a 16) (after a 18) with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok g3 =>
  cases h4 : cbField (after a 19) (after a 22) with
  | error err => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok g4 =>
  cases h5 : cbField (after a 24) (after a 27) with
  | error err => simp [h1, h2, h3, h4, h5, bind, Except.bind] at hg
  | ok g5 =>
  cases h6 : cbField (after a 29) (after a 31) with
  | error err => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at hg
  | ok g6 =>
  cases h7 : cbField (after a 31) (after a 34) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, bind, Except.bind] at hg
  | ok g7 =>
  cases h8 : cbField (after a 34) (after a 38) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind] at hg
  | ok g8 =>
  cases h9 : cbField (after a 35) (after a 38) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind] at hg
  | ok g9 =>
  cases h10 : cbField (after a 40) (after a 43) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, bind, Except.bind] at hg
  | ok g10 =>
  cases h11 : cbField (after a 45) (after a 48) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, bind, Except.bind] at hg
  | ok g11 =>
  cases h12 : cbField (after a 50) (after a 53) with
  | error err =>
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, bind, Except.bind] at hg
  | ok g12 =>
  cases h13 : cbField (after a 55) (after a 57) with
  | error err =>
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, bind, Except.bind] at hg
  | ok g13 =>
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq] at hg
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hg.symm⟩

/-! ## Steps and short runs -/

section Runs

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- A step of `AND Xd, Xn, Xm`. -/
theorem step_andReg {s : State} {d n m : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.andReg d n m))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n &&& s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- A step of `ORR Xd, Xn, Xm`. -/
theorem step_orrReg {s : State} {d n m : Fin 32} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.orrReg d n m))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n ||| s.x m ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc rfl

/-- `MOVZ Xt, #m` and `AND Xd, Xr, Xt`: X`d` holds X`r` masked by `m`. -/
theorem run_movzAnd {a : UInt64} {d r t : Fin 32} {m : Fin 65536} (hd : d.val < 31)
    (ht : t.val < 31) (hrt : r ≠ t) (hcode : CodeAt code a [.movz t m 0, .andReg d r t])
    {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 2 ∧ u.x d = s.x r &&& UInt64.ofNat m.val ∧
      (∀ q : Fin 32, q ≠ d → q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_movz P code (s := s) (d := t) (imm := m)
    (hw := 0) ht (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_andReg P code (s := u1) (d := d) (n := r)
    (m := t) hd (by rw [q1]; exact c1)
  exact ⟨u2, r1.trans r2, by rw [p2, q1, ← after_succ],
    by rw [x2, x1, k1 r hrt, movz0_val], fun q hqd hqt => by rw [k2 q hqd, k1 q hqt],
    by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩

/-- `MOVZ Xt, #v` and `ORR Xd, Xr, Xt`: X`d` holds X`r` with the bits of `v`. -/
theorem run_movzOrr {a : UInt64} {d r t : Fin 32} {v : Fin 65536} (hd : d.val < 31)
    (ht : t.val < 31) (hrt : r ≠ t) (hcode : CodeAt code a [.movz t v 0, .orrReg d r t])
    {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 2 ∧ u.x d = s.x r ||| UInt64.ofNat v.val ∧
      (∀ q : Fin 32, q ≠ d → q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_movz P code (s := s) (d := t) (imm := v)
    (hw := 0) ht (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_orrReg P code (s := u1) (d := d) (n := r)
    (m := t) hd (by rw [q1]; exact c1)
  exact ⟨u2, r1.trans r2, by rw [p2, q1, ← after_succ],
    by rw [x2, x1, k1 r hrt, movz0_val], fun q hqd hqt => by rw [k2 q hqd, k1 q hqt],
    by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩

/-- `MOVZ Xt, #v0`, `CBZ Xr` past the next word, and `MOVZ Xt, #v1`: X`t` holds `v0` when X`r`
is zero and `v1` otherwise. -/
theorem run_movzCbz {a : UInt64} {t r : Fin 32} {v0 v1 : Fin 65536} {g : Fin 524288}
    (ht : t.val < 31) (hrt : r ≠ t)
    (hcode : CodeAt code a [.movz t v0 0, .cbz r g, .movz t v1 0])
    (hg : cbField (after a 1) (after a 3) = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 3 ∧
      u.x t = (if s.x r = 0 then UInt64.ofNat v0.val else UInt64.ofNat v1.val) ∧
      (∀ q : Fin 32, q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧ u.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_movz P code (s := s) (d := t) (imm := v0)
    (hw := 0) ht (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbz P code (s := u1) (r := r)
    (target := after a 3) (by rw [q1]; exact c1) (by rw [q1]; exact cbField_target hg)
  rw [k1 r hrt, q1, ← after_succ] at p2
  by_cases h0 : s.x r = 0
  · rw [ite_eq_left h0] at p2
    exact ⟨u2, r1.trans r2, p2, by rw [k2, x1, movz0_val, ite_eq_left h0],
      fun q hq => by rw [k2, k1 q hq], by rw [sp2, sp1], by rw [m2, m1], by rw [io2, io1]⟩
  · rw [ite_eq_right h0] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := t) (imm := v1)
      (hw := 0) ht (by rw [p2]; exact c2)
    exact ⟨u3, r1.trans (r2.trans r3), by rw [p3, p2, ← after_succ],
      by rw [x3, movz0_val, ite_eq_right h0], fun q hq => by rw [k3 q hq, k2, k1 q hq],
      by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1]⟩

/-- `CBZ Xr` past `MOVZ Xt, #v` and `ORR Xd, Xd, Xt`: X`d` gains the bits of `v` when X`r` is
nonzero. -/
theorem run_cbzOrr {a : UInt64} {r d t : Fin 32} {v : Fin 65536} {g : Fin 524288}
    (hd : d.val < 31) (ht : t.val < 31) (hdt : d ≠ t)
    (hcode : CodeAt code a [.cbz r g, .movz t v 0, .orrReg d d t])
    (hg : cbField a (after a 3) = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 3 ∧
      u.x d = s.x d ||| (if s.x r = 0 then 0 else UInt64.ofNat v.val) ∧
      (∀ q : Fin 32, q ≠ d → q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have hc := (CodeAt.cons (code := code)).mp hcode
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbz P code (s := s) (r := r)
    (target := after a 3) (by rw [hpc]; exact hc.1) (by rw [hpc]; exact cbField_target hg)
  by_cases h0 : s.x r = 0
  · rw [ite_eq_left h0] at p1
    exact ⟨u1, r1, p1, by rw [k1, ite_eq_left h0, UInt64.or_zero], fun q _ _ => k1 q, sp1, m1,
      io1⟩
  · rw [ite_eq_right h0, hpc, ← after_one] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzOrr P code (r := d) hd ht hdt hc.2 p1
    exact ⟨u2, r1.trans r2, by rw [p2, after_after], by rw [x2, k1, ite_eq_right h0],
      fun q hqd hqt => by rw [k2 q hqd hqt, k1], by rw [sp2, sp1], by rw [m2, m1],
      by rw [io2, io1]⟩

/-- `CBNZ Xr` past `MOVZ Xt, #v` and `ORR Xd, Xd, Xt`: X`d` gains the bits of `v` when X`r` is
zero. -/
theorem run_cbnzOrr {a : UInt64} {r d t : Fin 32} {v : Fin 65536} {g : Fin 524288}
    (hd : d.val < 31) (ht : t.val < 31) (hdt : d ≠ t)
    (hcode : CodeAt code a [.cbnz r g, .movz t v 0, .orrReg d d t])
    (hg : cbField a (after a 3) = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 3 ∧
      u.x d = s.x d ||| (if s.x r = 0 then UInt64.ofNat v.val else 0) ∧
      (∀ q : Fin 32, q ≠ d → q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have hc := (CodeAt.cons (code := code)).mp hcode
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbnz P code (s := s) (r := r)
    (target := after a 3) (by rw [hpc]; exact hc.1) (by rw [hpc]; exact cbField_target hg)
  by_cases h0 : s.x r = 0
  · rw [ite_eq_right (show ¬(s.x r ≠ 0) from fun h => h h0), hpc, ← after_one] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzOrr P code (r := d) hd ht hdt hc.2 p1
    exact ⟨u2, r1.trans r2, by rw [p2, after_after], by rw [x2, k1, ite_eq_left h0],
      fun q hqd hqt => by rw [k2 q hqd hqt, k1], by rw [sp2, sp1], by rw [m2, m1],
      by rw [io2, io1]⟩
  · rw [ite_eq_left (show s.x r ≠ 0 from h0)] at p1
    exact ⟨u1, r1, p1, by rw [k1, ite_eq_right h0, UInt64.or_zero], fun q _ _ => k1 q, sp1, m1,
      io1⟩

/-- The test of the bits `m` of X`r` through X`t` with `CBZ`, and `ORR` of `v` into X`d` when
any of them is set. -/
theorem run_andCbzOrr {a : UInt64} {r t d : Fin 32} {m v : Fin 65536} {g : Fin 524288}
    (hd : d.val < 31) (ht : t.val < 31) (hdt : d ≠ t) (hrt : r ≠ t)
    (hcode : CodeAt code a [.movz t m 0, .andReg t r t, .cbz t g, .movz t v 0, .orrReg d d t])
    (hg : cbField (after a 2) (after a 5) = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 5 ∧
      u.x d = s.x d ||| (if s.x r &&& UInt64.ofNat m.val = 0 then 0 else UInt64.ofNat v.val) ∧
      (∀ q : Fin 32, q ≠ d → q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have hc := CodeAt.split code hcode (l1 := [.movz t m 0, .andReg t r t]) (n := 2) rfl
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movzAnd P code ht ht hrt hc.1 hpc
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_cbzOrr P code hd ht hdt hc.2
    (by rw [after_after]; exact hg) p1
  exact ⟨u2, r1.trans r2, by rw [p2, after_after], by rw [x2, x1, k1 d hdt hdt],
    fun q hqd hqt => by rw [k2 q hqd hqt, k1 q hqt hqt], by rw [sp2, sp1], by rw [m2, m1],
    by rw [io2, io1]⟩

/-- The test of the bits `m` of X`r` through X`t` with `CBNZ`, and `ORR` of `v` into X`d` when
none of them is set. -/
theorem run_andCbnzOrr {a : UInt64} {r t d : Fin 32} {m v : Fin 65536} {g : Fin 524288}
    (hd : d.val < 31) (ht : t.val < 31) (hdt : d ≠ t) (hrt : r ≠ t)
    (hcode : CodeAt code a [.movz t m 0, .andReg t r t, .cbnz t g, .movz t v 0, .orrReg d d t])
    (hg : cbField (after a 2) (after a 5) = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 5 ∧
      u.x d = s.x d ||| (if s.x r &&& UInt64.ofNat m.val = 0 then UInt64.ofNat v.val else 0) ∧
      (∀ q : Fin 32, q ≠ d → q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have hc := CodeAt.split code hcode (l1 := [.movz t m 0, .andReg t r t]) (n := 2) rfl
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movzAnd P code ht ht hrt hc.1 hpc
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_cbnzOrr P code hd ht hdt hc.2
    (by rw [after_after]; exact hg) p1
  exact ⟨u2, r1.trans r2, by rw [p2, after_after], by rw [x2, x1, k1 d hdt hdt],
    fun q hqd hqt => by rw [k2 q hqd hqt, k1 q hqt hqt], by rw [sp2, sp1], by rw [m2, m1],
    by rw [io2, io1]⟩

/-! ## The parts of `openHow` -/

/-- The access mode of `openHow`, from its eleventh word: X24 gains `O_WRONLY` (1) when the
rights lack `fd_read` (2) and hold `fd_write` (64), and `O_RDWR` (2) otherwise. -/
theorem run_openHowMode {a : UInt64} {g2 g3 : Fin 524288}
    (hcode : CodeAt code a [.movz 9 1 0, .movz 10 2 0, .andReg 10 5 10, .cbnz 10 g2,
      .movz 10 64 0, .andReg 10 5 10, .cbnz 10 g3, .movz 9 2 0, .orrReg 24 24 9])
    (hg2 : cbField (after a 3) (after a 7) = .ok g2)
    (hg3 : cbField (after a 6) (after a 8) = .ok g3) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 9 ∧
      u.x 24 = s.x 24 ||| (if s.x 5 &&& 2 = 0 ∧ s.x 5 &&& 64 ≠ 0 then 1 else 2) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 24 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c3 := hcode 3 (by simp)
  have c6 := hcode 6 (by simp)
  have c8 := hcode 8 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c3 c6 c8
  have c12 : CodeAt code (after a 1) [.movz 10 2 0, .andReg 10 5 10] := by
    simpa using CodeAt.drop_take code hcode 1 2 (by simp)
  have c45 : CodeAt code (after a 4) [.movz 10 64 0, .andReg 10 5 10] := by
    simpa using CodeAt.drop_take code hcode 4 2 (by simp)
  have c78 : CodeAt code (after a 7) [.movz 9 2 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 7 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_movz P code (s := s) (d := 9) (imm := 1)
    (hw := 0) (by decide) (by rw [hpc]; exact c0)
  rw [movz0_val, show UInt64.ofNat (1 : Fin 65536).val = 1 from rfl] at x1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzAnd P code (d := 10) (r := 5) (t := 10)
    (m := 2) (by decide) (by decide) (by decide) c12 (s := u1) (by rw [p1, hpc, after_one])
  rw [show UInt64.ofNat (2 : Fin 65536).val = 2 from rfl, k1 5 (by decide)] at x2
  have q2 : u2.pc = after a 3 := by rw [p2, after_after]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_cbnz P code (s := u2) (r := 10)
    (target := after a 7) (by rw [q2]; exact c3) (by rw [q2]; exact cbField_target hg2)
  rw [x2, q2, ← after_succ] at p3
  have hx3 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → u3.x q = s.x q := fun q h9 h10 => by
    rw [k3, k2 q h10 h10, k1 q h9]
  have h9v : u3.x 9 = 1 := by rw [k3, k2 9 (by decide) (by decide), x1]
  have hr3 : Reach P code s u3 := r1.trans (r2.trans r3)
  have hsp3 : u3.sp = s.sp := by rw [sp3, sp2, sp1]
  have hm3 : u3.mem = s.mem := by rw [m3, m2, m1]
  have hio3 : u3.io = s.io := by rw [io3, io2, io1]
  by_cases h2 : s.x 5 &&& 2 = 0
  · rw [ite_eq_right (show ¬(s.x 5 &&& 2 ≠ 0) from fun h => h h2)] at p3
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_movzAnd P code (d := 10) (r := 5) (t := 10)
      (m := 64) (by decide) (by decide) (by decide) c45 (s := u3) p3
    rw [show UInt64.ofNat (64 : Fin 65536).val = 64 from rfl, hx3 5 (by decide) (by decide)]
      at x4
    have q4 : u4.pc = after a 6 := by rw [p4, after_after]
    obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_cbnz P code (s := u4) (r := 10)
      (target := after a 8) (by rw [q4]; exact c6) (by rw [q4]; exact cbField_target hg3)
    rw [x4, q4, ← after_succ] at p5
    by_cases h64 : s.x 5 &&& 64 = 0
    · rw [ite_eq_right (show ¬(s.x 5 &&& 64 ≠ 0) from fun h => h h64)] at p5
      obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := run_movzOrr P code (d := 24) (r := 24)
        (t := 9) (v := 2) (by decide) (by decide) (by decide) c78 (s := u5) p5
      rw [show UInt64.ofNat (2 : Fin 65536).val = 2 from rfl] at x6
      refine ⟨u6, hr3.trans (r4.trans (r5.trans r6)), by rw [p6, after_after], ?_,
        fun q h9 h10 h24 => by rw [k6 q h24 h9, k5, k4 q h10 h10, hx3 q h9 h10],
        by rw [sp6, sp5, sp4, hsp3], by rw [m6, m5, m4, hm3], by rw [io6, io5, io4, hio3]⟩
      rw [x6, k5, k4 24 (by decide) (by decide), hx3 24 (by decide) (by decide),
        ite_eq_right (show ¬(s.x 5 &&& 2 = 0 ∧ s.x 5 &&& 64 ≠ 0) from fun h => h.2 h64)]
    · rw [ite_eq_left (show s.x 5 &&& 64 ≠ 0 from h64)] at p5
      obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_orrReg P code (s := u5) (d := 24)
        (n := 24) (m := 9) (by decide) (by rw [p5]; exact c8)
      refine ⟨u6, hr3.trans (r4.trans (r5.trans r6)), by rw [p6, p5, ← after_succ], ?_,
        fun q h9 h10 h24 => by rw [k6 q h24, k5, k4 q h10 h10, hx3 q h9 h10],
        by rw [sp6, sp5, sp4, hsp3], by rw [m6, m5, m4, hm3], by rw [io6, io5, io4, hio3]⟩
      rw [x6, k5, k5, k4 24 (by decide) (by decide), k4 9 (by decide) (by decide),
        hx3 24 (by decide) (by decide), h9v,
        ite_eq_left (show s.x 5 &&& 2 = 0 ∧ s.x 5 &&& 64 ≠ 0 from ⟨h2, h64⟩)]
  · rw [ite_eq_left (show s.x 5 &&& 2 ≠ 0 from h2)] at p3
    obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_movzOrr P code (d := 24) (r := 24) (t := 9)
      (v := 2) (by decide) (by decide) (by decide) c78 (s := u3) p3
    rw [show UInt64.ofNat (2 : Fin 65536).val = 2 from rfl] at x4
    refine ⟨u4, hr3.trans r4, by rw [p4, after_after], ?_,
      fun q h9 h10 h24 => by rw [k4 q h24 h9, hx3 q h9 h10], by rw [sp4, hsp3],
      by rw [m4, hm3], by rw [io4, hio3]⟩
    rw [x4, hx3 24 (by decide) (by decide),
      ite_eq_right (show ¬(s.x 5 &&& 2 = 0 ∧ s.x 5 &&& 64 ≠ 0) from fun h => h2 h.1)]

/-- The words of `openHow` up to the creation flags: X24 holds `O_CLOEXEC` (`0x80000`) with the
access mode when the rights hold `fd_write` or the `oflags` hold `creat` (1) or `trunc` (8), and
X25 and X27 hold the `oflags`' bits `creat` and `trunc`. -/
theorem run_openHowAccess {a : UInt64} {g1 g2 g3 : Fin 524288}
    (hcode : CodeAt code a [.movz 24 8 1, .movz 9 1 0, .andReg 25 4 9, .movz 9 8 0,
      .andReg 27 4 9, .movz 9 64 0, .andReg 28 5 9, .orrReg 28 28 25, .orrReg 28 28 27,
      .cbz 28 g1, .movz 9 1 0, .movz 10 2 0, .andReg 10 5 10, .cbnz 10 g2, .movz 10 64 0,
      .andReg 10 5 10, .cbnz 10 g3, .movz 9 2 0, .orrReg 24 24 9])
    (hg1 : cbField (after a 9) (after a 19) = .ok g1)
    (hg2 : cbField (after a 13) (after a 17) = .ok g2)
    (hg3 : cbField (after a 16) (after a 18) = .ok g3) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 19 ∧
      u.x 24 = 0x80000 ||| (if s.x 5 &&& 64 ||| s.x 4 &&& 1 ||| s.x 4 &&& 8 = 0 then 0
        else if s.x 5 &&& 2 = 0 ∧ s.x 5 &&& 64 ≠ 0 then 1 else 2) ∧
      u.x 25 = s.x 4 &&& 1 ∧ u.x 27 = s.x 4 &&& 8 ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 24 → q ≠ 25 → q ≠ 27 → q ≠ 28 → u.x q = s.x q) ∧
      u.sp = s.sp ∧ u.mem = s.mem ∧ u.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c7 := hcode 7 (by simp)
  have c8 := hcode 8 (by simp)
  have c9 := hcode 9 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c7 c8 c9
  have c12 : CodeAt code (after a 1) [.movz 9 1 0, .andReg 25 4 9] := by
    simpa using CodeAt.drop_take code hcode 1 2 (by simp)
  have c34 : CodeAt code (after a 3) [.movz 9 8 0, .andReg 27 4 9] := by
    simpa using CodeAt.drop_take code hcode 3 2 (by simp)
  have c56 : CodeAt code (after a 5) [.movz 9 64 0, .andReg 28 5 9] := by
    simpa using CodeAt.drop_take code hcode 5 2 (by simp)
  have cm : CodeAt code (after a 10) [.movz 9 1 0, .movz 10 2 0, .andReg 10 5 10, .cbnz 10 g2,
      .movz 10 64 0, .andReg 10 5 10, .cbnz 10 g3, .movz 9 2 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 10 9 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_movz P code (s := s) (d := 24) (imm := 8)
    (hw := 1) (by decide) (by rw [hpc]; exact c0)
  rw [show UInt64.ofNat (8 : Fin 65536).val <<< UInt64.ofNat (16 * (1 : Fin 4).val) = 0x80000
    by decide] at x1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzAnd P code (d := 25) (r := 4) (t := 9)
    (m := 1) (by decide) (by decide) (by decide) c12 (s := u1) (by rw [p1, hpc, after_one])
  rw [show UInt64.ofNat (1 : Fin 65536).val = 1 from rfl] at x2
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_movzAnd P code (d := 27) (r := 4) (t := 9)
    (m := 8) (by decide) (by decide) (by decide) c34 (s := u2) (by rw [p2, after_after])
  rw [show UInt64.ofNat (8 : Fin 65536).val = 8 from rfl] at x3
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_movzAnd P code (d := 28) (r := 5) (t := 9)
    (m := 64) (by decide) (by decide) (by decide) c56 (s := u3) (by rw [p3, after_after])
  rw [show UInt64.ofNat (64 : Fin 65536).val = 64 from rfl] at x4
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_orrReg P code (s := u4) (d := 28) (n := 28)
    (m := 25) (by decide) (by rw [p4, after_after]; exact c7)
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_orrReg P code (s := u5) (d := 28) (n := 28)
    (m := 27) (by decide) (by rw [p5, p4, after_after, ← after_succ]; exact c8)
  have q6 : u6.pc = after a 9 := by rw [p6, p5, p4, after_after, ← after_succ, ← after_succ]
  obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := step_cbz P code (s := u6) (r := 28)
    (target := after a 19) (by rw [q6]; exact c9) (by rw [q6]; exact cbField_target hg1)
  have f6 : ∀ q : Fin 32, q ≠ 9 → q ≠ 24 → q ≠ 25 → q ≠ 27 → q ≠ 28 → u6.x q = s.x q :=
    fun q h9 h24 h25 h27 h28 => by
      rw [k6 q h28, k5 q h28, k4 q h28 h9, k3 q h27 h9, k2 q h25 h9, k1 q h24]
  have e24 : u6.x 24 = 0x80000 := by simp (disch := decide) only [k6, k5, k4, k3, k2, x1]
  have e25 : u6.x 25 = s.x 4 &&& 1 := by simp (disch := decide) only [k6, k5, k4, k3, x2, k1]
  have e27 : u6.x 27 = s.x 4 &&& 8 := by simp (disch := decide) only [k6, k5, k4, x3, k2, k1]
  have e28 : u6.x 28 = s.x 5 &&& 64 ||| s.x 4 &&& 1 ||| s.x 4 &&& 8 := by
    simp (disch := decide) only [x6, x5, x4, x3, x2, k5, k4, k3, k2, k1]
  have hr7 : Reach P code s u7 :=
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7)))))
  have hsp7 : u7.sp = s.sp := by rw [sp7, sp6, sp5, sp4, sp3, sp2, sp1]
  have hm7 : u7.mem = s.mem := by rw [m7, m6, m5, m4, m3, m2, m1]
  have hio7 : u7.io = s.io := by rw [io7, io6, io5, io4, io3, io2, io1]
  by_cases hw : s.x 5 &&& 64 ||| s.x 4 &&& 1 ||| s.x 4 &&& 8 = 0
  · rw [e28, ite_eq_left hw] at p7
    exact ⟨u7, hr7, p7, by rw [k7, e24, ite_eq_left hw, UInt64.or_zero], by rw [k7, e25],
      by rw [k7, e27], fun q h9 _ h24 h25 h27 h28 => by rw [k7, f6 q h9 h24 h25 h27 h28],
      hsp7, hm7, hio7⟩
  · rw [e28, ite_eq_right hw, q6, ← after_succ] at p7
    obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := run_openHowMode P code cm
      (by simp only [after_after]; exact hg2) (by simp only [after_after]; exact hg3) p7
    exact ⟨u8, hr7.trans r8, by rw [p8, after_after],
      by rw [x8, k7, k7, e24, f6 5 (by decide) (by decide) (by decide) (by decide) (by decide),
        ite_eq_right hw],
      by rw [k8 25 (by decide) (by decide) (by decide), k7, e25],
      by rw [k8 27 (by decide) (by decide) (by decide), k7, e27],
      fun q h9 h10 h24 h25 h27 h28 => by rw [k8 q h9 h10 h24, k7, f6 q h9 h24 h25 h27 h28],
      by rw [sp8, hsp7], by rw [m8, hm7], by rw [io8, hio7]⟩

/-- `excl` with `creat`: X26 holds the `oflags` in X4 masked by `excl` (4) when X25 is nonzero,
and 0 otherwise. -/
theorem run_openHowExcl {a : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.movz 9 4 0, .andReg 26 4 9, .cbnz 25 g, .movz 26 0 0])
    (hg : cbField (after a 2) (after a 4) = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 4 ∧
      u.x 26 = (if s.x 25 = 0 then 0 else s.x 4 &&& 4) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 26 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have hc := CodeAt.split code hcode (l1 := [.movz 9 4 0, .andReg 26 4 9]) (n := 2) rfl
  have c2 := hc.2 0 (by simp)
  have c3 := hc.2 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after] at c2 c3
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_movzAnd P code (d := 26) (r := 4) (t := 9)
    (m := 4) (by decide) (by decide) (by decide) hc.1 hpc
  rw [show UInt64.ofNat (4 : Fin 65536).val = 4 from rfl] at x1
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := step_cbnz P code (s := u1) (r := 25)
    (target := after a 4) (by rw [p1]; exact c2) (by rw [p1]; exact cbField_target hg)
  rw [k1 25 (by decide) (by decide)] at p2
  by_cases h0 : s.x 25 = 0
  · rw [ite_eq_right (show ¬(s.x 25 ≠ 0) from fun h => h h0)] at p2
    obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_movz P code (s := u2) (d := 26) (imm := 0)
      (hw := 0) (by decide) (by rw [p2, p1, ← after_succ]; exact c3)
    rw [movz0_val, show UInt64.ofNat (0 : Fin 65536).val = 0 from rfl] at x3
    exact ⟨u3, r1.trans (r2.trans r3), by rw [p3, p2, p1, ← after_succ, ← after_succ],
      by rw [x3, ite_eq_left h0],
      fun q h9 h26 => by rw [k3 q h26, k2, k1 q h26 h9], by rw [sp3, sp2, sp1],
      by rw [m3, m2, m1], by rw [io3, io2, io1]⟩
  · rw [ite_eq_left (show s.x 25 ≠ 0 from h0)] at p2
    exact ⟨u2, r1.trans r2, p2, by rw [k2, x1, ite_eq_right h0],
      fun q h9 h26 => by rw [k2, k1 q h26 h9], by rw [sp2, sp1], by rw [m2, m1],
      by rw [io2, io1]⟩

/-- `trunc` without `excl`: X24 gains `O_TRUNC` (`0x200`) when X27 is nonzero and X26 is zero. -/
theorem run_openHowTrunc {a : UInt64} {g8 g9 : Fin 524288}
    (hcode : CodeAt code a [.cbz 27 g8, .cbnz 26 g9, .movz 9 0x200 0, .orrReg 24 24 9])
    (hg8 : cbField a (after a 4) = .ok g8) (hg9 : cbField (after a 1) (after a 4) = .ok g9)
    {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 4 ∧
      u.x 24 = s.x 24 ||| (if s.x 27 = 0 then 0 else if s.x 26 = 0 then 0x200 else 0) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 24 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have hc := (CodeAt.cons (code := code)).mp hcode
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbz P code (s := s) (r := 27)
    (target := after a 4) (by rw [hpc]; exact hc.1) (by rw [hpc]; exact cbField_target hg8)
  by_cases h27 : s.x 27 = 0
  · rw [ite_eq_left h27] at p1
    exact ⟨u1, r1, p1, by rw [k1, ite_eq_left h27, UInt64.or_zero], fun q _ _ => k1 q, sp1, m1,
      io1⟩
  · rw [ite_eq_right h27, hpc, ← after_one] at p1
    obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_cbnzOrr P code (r := 26) (d := 24) (t := 9)
      (v := 0x200) (by decide) (by decide) (by decide) hc.2 (by rw [after_after]; exact hg9) p1
    rw [show UInt64.ofNat (0x200 : Fin 65536).val = 0x200 from rfl] at x2
    exact ⟨u2, r1.trans r2, by rw [p2, after_after], by rw [x2, k1, k1, ite_eq_right h27],
      fun q h9 h24 => by rw [k2 q h24 h9, k1], by rw [sp2, sp1], by rw [m2, m1],
      by rw [io2, io1]⟩

/-- The creation flags of `openHow`, from its twentieth word, with `creat` in X25 and `trunc` in
X27: `O_CREAT`, `O_DIRECTORY`, `O_EXCL`, and `O_TRUNC` into X24. -/
theorem run_openHowCreate {a : UInt64} {g4 g5 g6 g7 g8 g9 : Fin 524288}
    (hcode : CodeAt code a [.cbz 25 g4, .movz 9 0x40 0, .orrReg 24 24 9,
      .movz 9 2 0, .andReg 9 4 9, .cbz 9 g5, .movz 9 0x4000 0, .orrReg 24 24 9,
      .movz 9 4 0, .andReg 26 4 9, .cbnz 25 g6, .movz 26 0 0,
      .cbz 26 g7, .movz 9 0x80 0, .orrReg 24 24 9,
      .cbz 27 g8, .cbnz 26 g9, .movz 9 0x200 0, .orrReg 24 24 9])
    (hg4 : cbField a (after a 3) = .ok g4) (hg5 : cbField (after a 5) (after a 8) = .ok g5)
    (hg6 : cbField (after a 10) (after a 12) = .ok g6)
    (hg7 : cbField (after a 12) (after a 15) = .ok g7)
    (hg8 : cbField (after a 15) (after a 19) = .ok g8)
    (hg9 : cbField (after a 16) (after a 19) = .ok g9) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 19 ∧
      u.x 24 = s.x 24 ||| (if s.x 25 = 0 then 0 else 0x40) |||
        (if s.x 4 &&& 2 = 0 then 0 else 0x4000) |||
        (if (if s.x 25 = 0 then 0 else s.x 4 &&& 4) = 0 then 0 else 0x80) |||
        (if s.x 27 = 0 then 0
          else if (if s.x 25 = 0 then 0 else s.x 4 &&& 4) = 0 then 0x200 else 0) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 24 → q ≠ 26 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have c1 : CodeAt code a [.cbz 25 g4, .movz 9 0x40 0, .orrReg 24 24 9] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 3 (by simp)
  have c2 : CodeAt code (after a 3)
      [.movz 9 2 0, .andReg 9 4 9, .cbz 9 g5, .movz 9 0x4000 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 3 5 (by simp)
  have c3 : CodeAt code (after a 8) [.movz 9 4 0, .andReg 26 4 9, .cbnz 25 g6, .movz 26 0 0] := by
    simpa using CodeAt.drop_take code hcode 8 4 (by simp)
  have c4 : CodeAt code (after a 12) [.cbz 26 g7, .movz 9 0x80 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 12 3 (by simp)
  have c5 : CodeAt code (after a 15)
      [.cbz 27 g8, .cbnz 26 g9, .movz 9 0x200 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 15 4 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_cbzOrr P code (r := 25) (d := 24) (t := 9)
    (v := 0x40) (by decide) (by decide) (by decide) c1 hg4 hpc
  rw [show UInt64.ofNat (0x40 : Fin 65536).val = 0x40 from rfl] at x1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_andCbzOrr P code (r := 4) (t := 9) (d := 24)
    (m := 2) (v := 0x4000) (by decide) (by decide) (by decide) (by decide) c2
    (by simp only [after_after]; exact hg5) p1
  rw [show UInt64.ofNat (2 : Fin 65536).val = 2 from rfl,
    show UInt64.ofNat (0x4000 : Fin 65536).val = 0x4000 from rfl] at x2
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_openHowExcl P code c3
    (by simp only [after_after]; exact hg6) (by rw [p2, after_after])
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_cbzOrr P code (r := 26) (d := 24) (t := 9)
    (v := 0x80) (by decide) (by decide) (by decide) c4 (by simp only [after_after]; exact hg7)
    (by rw [p3, after_after])
  rw [show UInt64.ofNat (0x80 : Fin 65536).val = 0x80 from rfl] at x4
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_openHowTrunc P code c5
    (by simp only [after_after]; exact hg8) (by simp only [after_after]; exact hg9)
    (by rw [p4, after_after])
  refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), by rw [p5, after_after], ?_,
    fun q h9 h24 h26 => by rw [k5 q h9 h24, k4 q h24 h9, k3 q h9 h26, k2 q h24 h9, k1 q h24 h9],
    by rw [sp5, sp4, sp3, sp2, sp1], by rw [m5, m4, m3, m2, m1], by rw [io5, io4, io3, io2, io1]⟩
  simp (disch := decide) only [x5, x4, x3, x2, x1, k4, k3, k2, k1]

/-- `O_APPEND`, `O_NONBLOCK`, and `O_NOFOLLOW` of `openHow`, from its thirty-ninth word, into X24
from the `fdflags` in X7 and the `dirflags` in X1. -/
theorem run_openHowTail {a : UInt64} {g10 g11 g12 : Fin 524288}
    (hcode : CodeAt code a [.movz 9 1 0, .andReg 9 7 9, .cbz 9 g10, .movz 9 0x400 0,
      .orrReg 24 24 9, .movz 9 4 0, .andReg 9 7 9, .cbz 9 g11, .movz 9 0x800 0, .orrReg 24 24 9,
      .movz 9 1 0, .andReg 9 1 9, .cbnz 9 g12, .movz 9 0x8000 0, .orrReg 24 24 9])
    (hg10 : cbField (after a 2) (after a 5) = .ok g10)
    (hg11 : cbField (after a 7) (after a 10) = .ok g11)
    (hg12 : cbField (after a 12) (after a 15) = .ok g12) {s : State} (hpc : s.pc = a) :
    ∃ u, Reach P code s u ∧ u.pc = after a 15 ∧
      u.x 24 = s.x 24 ||| (if s.x 7 &&& 1 = 0 then 0 else 0x400) |||
        (if s.x 7 &&& 4 = 0 then 0 else 0x800) ||| (if s.x 1 &&& 1 = 0 then 0x8000 else 0) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 24 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
      u.io = s.io := by
  have c1 : CodeAt code a
      [.movz 9 1 0, .andReg 9 7 9, .cbz 9 g10, .movz 9 0x400 0, .orrReg 24 24 9] := by
    simpa [after_zero] using CodeAt.drop_take code hcode 0 5 (by simp)
  have c2 : CodeAt code (after a 5)
      [.movz 9 4 0, .andReg 9 7 9, .cbz 9 g11, .movz 9 0x800 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 5 5 (by simp)
  have c3 : CodeAt code (after a 10)
      [.movz 9 1 0, .andReg 9 1 9, .cbnz 9 g12, .movz 9 0x8000 0, .orrReg 24 24 9] := by
    simpa using CodeAt.drop_take code hcode 10 5 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := run_andCbzOrr P code (r := 7) (t := 9) (d := 24)
    (m := 1) (v := 0x400) (by decide) (by decide) (by decide) (by decide) c1 hg10 hpc
  rw [show UInt64.ofNat (1 : Fin 65536).val = 1 from rfl,
    show UInt64.ofNat (0x400 : Fin 65536).val = 0x400 from rfl] at x1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_andCbzOrr P code (r := 7) (t := 9) (d := 24)
    (m := 4) (v := 0x800) (by decide) (by decide) (by decide) (by decide) c2
    (by simp only [after_after]; exact hg11) p1
  rw [show UInt64.ofNat (4 : Fin 65536).val = 4 from rfl,
    show UInt64.ofNat (0x800 : Fin 65536).val = 0x800 from rfl] at x2
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_andCbnzOrr P code (r := 1) (t := 9)
    (d := 24) (m := 1) (v := 0x8000) (by decide) (by decide) (by decide) (by decide) c3
    (by simp only [after_after]; exact hg12) (by rw [p2, after_after])
  rw [show UInt64.ofNat (1 : Fin 65536).val = 1 from rfl,
    show UInt64.ofNat (0x8000 : Fin 65536).val = 0x8000 from rfl] at x3
  refine ⟨u3, r1.trans (r2.trans r3), by rw [p3, after_after], ?_,
    fun q h9 h24 => by rw [k3 q h24 h9, k2 q h24 h9, k1 q h24 h9], by rw [sp3, sp2, sp1],
    by rw [m3, m2, m1], by rw [io3, io2, io1]⟩
  simp (disch := decide) only [x3, x2, x1, k2, k1]

/-- The stores of `openHow`, from its fifty-fourth word: the flags word in X24, the mode 438
when X25 is nonzero and 0 otherwise, and the resolution 10, as 24 bytes 1,056 bytes above X20. -/
theorem run_openHowStores {a : UInt64} {g : Fin 524288}
    (hcode : CodeAt code a [.str 24 20 132, .movz 9 0 0, .cbz 25 g, .movz 9 438 0,
      .str 9 20 133, .movz 9 10 0, .str 9 20 134])
    (hg : cbField (after a 2) (after a 4) = .ok g) {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 24, P.normal (s.x 20 + UInt64.ofNat (1056 + k)) = true) :
    ∃ u, Reach P code s u ∧ u.pc = after a 7 ∧ (∀ q : Fin 32, q ≠ 9 → u.x q = s.x q) ∧
      u.sp = s.sp ∧ u.io = s.io ∧
      u.mem = writeList s.mem (s.x 20 + UInt64.ofNat 1056)
        ((List.range 8).map (Verified.Wasi.byteOf (s.x 24).toNat) ++
          (List.range 8).map
            (Verified.Wasi.byteOf (if s.x 25 = 0 then (0 : UInt64) else 438).toNat) ++
          (List.range 8).map (Verified.Wasi.byteOf (10 : UInt64).toNat)) := by
  have c0 := hcode 0 (by simp)
  have c4 := hcode 4 (by simp)
  have c5 := hcode 5 (by simp)
  have c6 := hcode 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c4 c5 c6
  have cs : CodeAt code (after a 1) [.movz 9 0 0, .cbz 25 g, .movz 9 438 0] := by
    simpa using CodeAt.drop_take code hcode 1 3 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_str P code (s := s) (t := 24) (n := 20)
    (i := 132) (by decide) (by decide) (by rw [hpc]; exact c0)
    (fun k hk => by rw [show 8 * 132 + k = 1056 + k by omega]; exact hmap k (by omega))
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_movzCbz P code (t := 9) (r := 25) (v0 := 0)
    (v1 := 438) (by decide) (by decide) cs (by simp only [after_after]; exact hg)
    (by rw [p1, hpc, after_one])
  rw [show UInt64.ofNat (0 : Fin 65536).val = 0 from rfl,
    show UInt64.ofNat (438 : Fin 65536).val = 438 from rfl, k1 25] at x2
  have q2 : u2.pc = after a 4 := by rw [p2, after_after]
  have h20 : u2.x 20 = s.x 20 := by rw [k2 20 (by decide), k1]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_str P code (s := u2) (t := 9) (n := 20)
    (i := 133) (by decide) (by decide) (by rw [q2]; exact c4)
    (fun k hk => by
      rw [h20, show 8 * 133 + k = 1056 + (8 + k) by omega]; exact hmap (8 + k) (by omega))
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_movz P code (s := u3) (d := 9) (imm := 10)
    (hw := 0) (by decide) (by rw [p3, q2, ← after_succ]; exact c5)
  rw [movz0_val, show UInt64.ofNat (10 : Fin 65536).val = 10 from rfl] at x4
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := step_str P code (s := u4) (t := 9) (n := 20)
    (i := 134) (by decide) (by decide) (by rw [p4, p3, q2, ← after_succ, ← after_succ]; exact c6)
    (fun k hk => by
      rw [k4 20 (by decide), k3, h20, show 8 * 134 + k = 1056 + (16 + k) by omega]
      exact hmap (16 + k) (by omega))
  have a1 : s.x 20 + UInt64.ofNat (8 * 133) = s.x 20 + UInt64.ofNat 1056 + UInt64.ofNat 8 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMul]
    omega
  have a2 : s.x 20 + UInt64.ofNat (8 * 134) = s.x 20 + UInt64.ofNat 1056 + UInt64.ofNat 16 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMul]
    omega
  refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))),
    by rw [p5, p4, p3, q2, ← after_succ, ← after_succ, ← after_succ],
    fun q h9 => by rw [k5, k4 q h9, k3, k2 q h9, k1], by rw [sp5, sp4, sp3, sp2, sp1],
    by rw [io5, io4, io3, io2, io1], ?_⟩
  rw [m5, x4, m4, k4 20 (by decide), k3, m3, x2, h20, m2, m1, a1, a2]
  exact store64_three s.mem (s.x 20 + UInt64.ofNat 1056) (s.x 24) _ _

/-! ## The run of `openHow` -/

/-- The run of `openHow` from its first word: the next word after its 60, X9, X10, and X24 to
X28 changed, and the 24 bytes of `openHowBytes arm64Flags` for the `dirflags` in X1, the
`oflags` in X4, the rights in X5, and the `fdflags` in X7 written 1,056 bytes above X20. -/
theorem run_openHow {a : UInt64} {is : List Instr} (hg : openHow a = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 24, P.normal (s.x 20 + UInt64.ofNat (1056 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.pc = after a 60 ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 24 → q ≠ 25 → q ≠ 26 → q ≠ 27 → q ≠ 28 →
        t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = writeList s.mem (s.x 20 + UInt64.ofNat 1056)
        (openHowBytes arm64Flags (s.x 1) (s.x 4) (s.x 5) (s.x 7)) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, rfl⟩ := openHow_ok hg
  have cA := CodeAt.split code hcode (n := 53) (by simp)
  have cB := CodeAt.split code cA.1 (n := 38) (by simp)
  have cC := CodeAt.split code cB.1 (n := 19) (by simp)
  obtain ⟨u1, r1, p1, x1, y1, z1, k1, sp1, m1, io1⟩ :=
    run_openHowAccess P code cC.1 h1 h2 h3 hpc
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_openHowCreate P code cC.2
    (by simp only [after_after]; exact h4) (by simp only [after_after]; exact h5)
    (by simp only [after_after]; exact h6) (by simp only [after_after]; exact h7)
    (by simp only [after_after]; exact h8) (by simp only [after_after]; exact h9) p1
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_openHowTail P code cB.2
    (by simp only [after_after]; exact h10) (by simp only [after_after]; exact h11)
    (by simp only [after_after]; exact h12) (by rw [p2, after_after])
  have e20 : u3.x 20 = s.x 20 := by simp (disch := decide) only [k3, k2, k1]
  have e25 : u3.x 25 = s.x 4 &&& 1 := by simp (disch := decide) only [k3, k2, y1]
  have e24 : u3.x 24 = openFlagsWord arm64Flags (s.x 1) (s.x 4) (s.x 5) (s.x 7) := by
    simp (disch := decide) only [x3, x2, x1, y1, z1, k2, k1]
    exact openHow_flags (s.x 1) (s.x 4) (s.x 5) (s.x 7)
  obtain ⟨u4, r4, p4, k4, sp4, io4, m4⟩ := run_openHowStores P code cA.2
    (by simp only [after_after]; exact h13) (by rw [p3, after_after])
    (fun k hk => by rw [e20]; exact hmap k hk)
  have e438 : (if s.x 4 &&& 1 = 0 then (0 : UInt64) else 438).toNat =
      if s.x 4 &&& 1 ≠ 0 then 438 else 0 := by
    by_cases h : s.x 4 &&& 1 = 0 <;> simp [h]
  refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), by rw [p4, after_after],
    fun q h9 h10 h24 h25 h26 h27 h28 => by
      rw [k4 q h9, k3 q h9 h24, k2 q h9 h24 h26, k1 q h9 h10 h24 h25 h27 h28],
    by rw [sp4, sp3, sp2, sp1], by rw [io4, io3, io2, io1], ?_⟩
  rw [m4, m3, m2, m1, e20, e24, e25, e438]
  rfl

end Runs

end Verified.ShimA64
