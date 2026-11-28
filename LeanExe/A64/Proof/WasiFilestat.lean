module

public import LeanExe.A64.Proof.WasiFiles

@[expose] public section

/-!
The runs of the stub of `fd_filestat_get` of `LeanExe/A64/WasiFiles.lean` in the program's model.
`filestatStub_ok` unpacks the generator, and `filestatStub_length` gives its size.
`run_filestatFront` follows the stub from its entry to the trap stub for a record beyond the
memory, to the return of errno 8 for a descriptor that the shim does not hold, or to the `BL` of
`statx` with its arguments set, the scratch's path buffer holding a zero byte, and the `statx`
record cleared (`run_zeroStores`).  `run_stampConvert` converts one `statx_timestamp` to
nanoseconds as `stampValue` states, and `run_filestatBack` follows the stub from the call's result
to the return or the trap stub: the error tail for a result other than 0, and for 0 the
conversions of `stampsValue`, the file type of `fileTypeOf`, and the eight words of
`filestatWords` stored at the record's guest address.
-/

namespace LeanExe.A64

open Wasm

/-! ## The generator's parts -/

/-- The instructions of `stampConvert` with the branch fields `g8` to the trap stub and `g14` to
the return of errno 61. -/
def stampCode (off : Fin 4096) (d : Fin 32) (g8 g14 : Fin 524288) : List Instr :=
  [.ldr 9 20 off, .ldr 10 20 (off + 1), .orrW 10 31 10] ++ movImm 11 999999999 ++
    [.subsReg 31 10 11, .bcond 8 g8, .addImm 11 11 1, .subReg 12 31 10, .subImm 12 12 1,
      .udiv 12 12 11, .subsReg 31 9 12, .bcond 8 g14, .madd d 9 11 10]

theorem stampConvert_ok {a tr ov : UInt64} {off : Fin 4096} {d : Fin 32} {is : List Instr}
    (hg : stampConvert a tr ov off d = .ok is) :
    ∃ g8 g14, cbField (after a 8) tr = .ok g8 ∧ cbField (after a 14) ov = .ok g14 ∧
      is = stampCode off d g8 g14 := by
  unfold stampConvert at hg
  cases h8 : cbField (after a 8) tr with
  | error err => simp [h8, bind, Except.bind] at hg
  | ok g8 =>
  cases h14 : cbField (after a 14) ov with
  | error err => simp [h8, h14, bind, Except.bind] at hg
  | ok g14 =>
  simp only [h8, h14, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨g8, g14, rfl, rfl, hg.symm⟩

/-- `STR` of the registers `rs` at the words from `base` above X13, one word each. -/
def strsFrom : Nat → List (Fin 32) → List Instr
  | _, [] => []
  | base, r :: rs => .str r 13 (Fin.ofNat 4096 base) :: strsFrom (base + 1) rs

/-- The file type, the loads, and the stores of the stub after its conversions, with the returns
of errno 0 and errno 61. -/
def recordCode : List Instr :=
  [.ldrb 10 20 1117, .lsrImm 10 10 4, .addReg 10 10 10, .addReg 10 10 10] ++
    movImm 11 filetypeTable ++
    [.lsrv 11 11 10, .movz 12 0xF 0, .andReg 11 11 12, .ldr 25 20 140, .ldr 26 20 138,
      .orrW 26 31 26, .ldr 27 20 141, .addReg 13 17 21, .movz 9 1 0] ++
    strsFrom 512 [9, 25, 11, 26, 27, 22, 23, 24] ++ [.movz 0 0 0, .ret 19, .movz 0 61 0, .ret 19]

/-- `n` stores of XZR at words `start` to `start + n − 1` above X20. -/
def zeroStores (start n : Nat) : List Instr :=
  (List.range n).map fun i => .str 31 20 (Fin.ofNat 4096 (start + i))

theorem statxClear_eq : statxClear = zeroStores 136 32 := rfl

theorem filestatStub_ok {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) :
    ∃ range held atime mtime btime tail gs g56 g93,
      rangeCheck (after a 1) tr = .ok range ∧ heldTest (after a 10) (after a 145) 0 = .ok held ∧
      stampConvert (after a 57) tr (after a 137) 144 22 = .ok atime ∧
      stampConvert (after a 73) tr (after a 137) 150 23 = .ok mtime ∧
      stampConvert (after a 94) tr (after a 137) 146 24 = .ok btime ∧
      errorTail (after a 139) tr en = .ok tail ∧ bField (after a 55) svc = .ok gs ∧
      cbField (after a 56) (after a 139) = .ok g56 ∧ cbField (after a 93) (after a 110) = .ok g93 ∧
      is = [.addImm 12 1 64] ++ range ++ scratchAddr sc ++ held ++
        [.orrReg 19 31 30, .orrReg 21 31 1, .strb 31 20 1080] ++ zeroStores 136 32 ++
        [.addImm 1 20 1080, .movz 2 0x1000 0, .movz 3 0xFFF 0, .addImm 4 20 1088, .movz 8 291 0,
          .bl gs, .cbnz 0 g56] ++ atime ++ mtime ++
        [.ldr 9 20 136, .movz 10 0x800 0, .andReg 9 9 10, .movz 24 0 0, .cbz 9 g93] ++ btime ++
        recordCode ++ tail ++ [.movz 0 8 0, .ret 30] := by
  unfold filestatStub at hg
  cases h1 : rangeCheck (after a 1) tr with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok range =>
  cases h2 : heldTest (after a 10) (after a 145) 0 with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok held =>
  cases h3 : stampConvert (after a 57) tr (after a 137) 144 22 with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok atime =>
  cases h4 : stampConvert (after a 73) tr (after a 137) 150 23 with
  | error err => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok mtime =>
  cases h5 : stampConvert (after a 94) tr (after a 137) 146 24 with
  | error err => simp [h1, h2, h3, h4, h5, bind, Except.bind] at hg
  | ok btime =>
  cases h6 : errorTail (after a 139) tr en with
  | error err => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at hg
  | ok tail =>
  cases h7 : bField (after a 55) svc with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, bind, Except.bind] at hg
  | ok gs =>
  cases h8 : cbField (after a 56) (after a 139) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind] at hg
  | ok g56 =>
  cases h9 : cbField (after a 93) (after a 110) with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind] at hg
  | ok g93 =>
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  refine ⟨range, held, atime, mtime, btime, tail, gs, g56, g93, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, ?_⟩
  rw [← hg]
  simp only [recordCode, statxClear_eq, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem filestatStub_length {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) : is.length = filestatStubSize := by
  obtain ⟨range, held, atime, mtime, btime, tail, gs, g56, g93, h1, h2, h3, h4, h5, h6, -, -, -,
    rfl⟩ := filestatStub_ok hg
  obtain ⟨_, _, rfl⟩ := rangeCheck_ok h1
  obtain ⟨_, _, _, _, rfl⟩ := heldTest_ok h2
  obtain ⟨_, _, _, _, rfl⟩ := stampConvert_ok h3
  obtain ⟨_, _, _, _, rfl⟩ := stampConvert_ok h4
  obtain ⟨_, _, _, _, rfl⟩ := stampConvert_ok h5
  obtain ⟨_, _, _, _, rfl⟩ := errorTail_ok h6
  rfl

section Runs

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## The clear of the `statx` record -/

/-- The memory `m` with `n` zero words stored from `a`, 8 bytes apart. -/
def zeroWords (m : UInt64 → UInt8) (a : UInt64) : Nat → UInt64 → UInt8
  | 0 => m
  | n + 1 => zeroWords (store64 m a 0) (a + 8) n

theorem zeroStores_succ (start n : Nat) :
    zeroStores start (n + 1) = .str 31 20 (Fin.ofNat 4096 start) :: zeroStores (start + 1) n := by
  unfold zeroStores
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  show Instr.str 31 20 (Fin.ofNat 4096 (start + (i + 1))) =
    Instr.str 31 20 (Fin.ofNat 4096 (start + 1 + i))
  rw [show start + (i + 1) = start + 1 + i by omega]

/-- The stores of `zeroStores start n` from `a`, with the `8 n` bytes from word `start` above X20
Normal memory, reach the next word with every register, SP, and the UART's state kept and the
memory with `n` zero words from X20 plus `8 start`. -/
theorem run_zeroStores : ∀ (n start : Nat) {a : UInt64} {s : State}, start + n ≤ 4096 →
    CodeAt code a (zeroStores start n) → s.pc = a →
    (∀ k < 8 * n, P.normal (s.x 20 + UInt64.ofNat (8 * start + k)) = true) →
    ∃ t, Reach P code s t ∧ t.pc = after a n ∧ (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.io = s.io ∧ t.mem = zeroWords s.mem (s.x 20 + UInt64.ofNat (8 * start)) n
  | 0, _, a, s, _, _, hpc, _ => ⟨s, .refl _, by rw [hpc, after_zero], fun _ => rfl, rfl, rfl, rfl⟩
  | n + 1, start, a, s, hb, hcode, hpc, hmap => by
    rw [zeroStores_succ] at hcode
    have c0 := (CodeAt.cons.mp hcode).1
    have hrest := (CodeAt.cons.mp hcode).2
    have hfin : (Fin.ofNat 4096 start : Fin 4096) = ⟨start, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hfin] at c0
    obtain ⟨u, ru, pu, ku, spu, mu, iou⟩ := step_str P code (s := s) (t := 31) (n := 20)
      (i := start) (by omega) (by decide) (by rw [hpc]; exact c0)
      (fun k hk => hmap k (by omega))
    obtain ⟨t, rt, pt, kt, spt, iot, mt⟩ := run_zeroStores n (start + 1) (s := u) (by omega) hrest
      (by rw [pu, hpc, after_one])
      (fun k hk => by
        rw [ku 20, show 8 * (start + 1) + k = 8 * start + (8 + k) by omega]
        exact hmap (8 + k) (by omega))
    refine ⟨t, ru.trans rt, by rw [pt, after_after, Nat.add_comm], fun q => by rw [kt, ku],
      by rw [spt, spu],
      by rw [iot, iou], ?_⟩
    rw [mt, mu, ku 20, zeroWords]
    congr 1
    rw [show 8 * (start + 1) = 8 * start + 8 by omega, ← add_ofNat_add]
    rfl

/-! ## The conversion of a timestamp -/

/-- The stub's conversion of a `statx_timestamp` whose first word is `sec` and whose second word
holds the nanoseconds in its low 32 bits: `none` for nanoseconds above `10^9 − 1`, `some none` for
seconds above `⌊(2^64 − 1 − nsec) / 10^9⌋`, and otherwise the time in nanoseconds. -/
def stampValue (sec ns : UInt64) : Option (Option UInt64) :=
  if 999999999 < ns.toUInt32.toUInt64 then none
  else if (0 - ns.toUInt32.toUInt64 - 1) / 1000000000 < sec then some none
  else some (some (ns.toUInt32.toUInt64 + sec * 1000000000))

/-- The conversion of the `statx_timestamp` at word `off` above X20, from `a`: the trap stub `tr`,
the return of errno 61 at `ov`, or `after a 16` with the time in X`d`, as `stampValue` of the
timestamp's two words states.  X9 to X12 and X`d` change, and the flags. -/
theorem run_stampConvert {a tr ov : UInt64} {off : Fin 4096} {d : Fin 32} {g8 g14 : Fin 524288}
    (hd : d.val < 31) (hoff : off.val + 1 < 4096) (hcode : CodeAt code a (stampCode off d g8 g14))
    (hg8 : cbField (after a 8) tr = .ok g8) (hg14 : cbField (after a 14) ov = .ok g14)
    {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < 16, P.normal (s.x 20 + UInt64.ofNat (8 * off.val + k)) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ d → t.x q = s.x q) ∧
      match stampValue (load64 s.mem (s.x 20 + UInt64.ofNat (8 * off.val)))
          (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (off.val + 1)))) with
      | none => t.pc = tr
      | some none => t.pc = ov
      | some (some v) => t.pc = after a 16 ∧ t.x d = v := by
  have c := fun k (hk : k < 16) => hcode k (by simp [stampCode, movImm]; omega)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c9 := c 9 (by omega)
  have c10 := c 10 (by omega)
  have c11 := c 11 (by omega)
  have c12 := c 12 (by omega)
  have c15 := c 15 (by omega)
  simp only [stampCode, movImm, List.getElem_cons_zero, List.getElem_cons_succ,
    List.cons_append, List.nil_append, after_zero] at c0 c1 c2 c9 c10 c11 c12 c15
  have hfin : off + 1 = ⟨off.val + 1, hoff⟩ := Fin.ext (by simp [Fin.val_add]; omega)
  rw [hfin] at c1
  have cmov : CodeAt code (after a 3) (movImm 11 999999999) := by
    simpa [stampCode, movImm] using CodeAt.drop_take code hcode 3 4 (by simp [stampCode, movImm])
  have c78 : CodeAt code (after a 7) [.subsReg 31 10 11, .bcond 8 g8] := by
    simpa [stampCode, movImm] using CodeAt.drop_take code hcode 7 2 (by simp [stampCode, movImm])
  have c1314 : CodeAt code (after a 13) [.subsReg 31 9 12, .bcond 8 g14] := by
    simpa [stampCode, movImm] using
      CodeAt.drop_take code hcode 13 2 (by simp [stampCode, movImm])
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldr P code (s := s) (t := 9) (n := 20)
    (i := off.val) off.isLt (by decide) (by decide) (by rw [hpc]; exact c0)
    (fun k hk => hmap k (by omega))
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_ldr P code (s := u1) (t := 10) (n := 20)
    (i := off.val + 1) hoff (by decide) (by decide) (by rw [q1]; exact c1)
    (fun k hk => by
      rw [k1 20 (by decide), show 8 * (off.val + 1) + k = 8 * off.val + (8 + k) by omega]
      exact hmap (8 + k) (by omega))
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_orrW P code (s := u2) (d := 10) (n := 10)
    (by decide) (by rw [q2]; exact c2)
  have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  generalize hsec : load64 s.mem (s.x 20 + UInt64.ofNat (8 * off.val)) = sec
  generalize hns : load64 s.mem (s.x 20 + UInt64.ofNat (8 * (off.val + 1))) = ns
  have u3x9 : u3.x 9 = sec := by rw [k3 9 (by decide), k2 9 (by decide), x1, ← hsec]
  have u3x10 : u3.x 10 = ns.toUInt32.toUInt64 := by
    rw [x3, x2, k1 20 (by decide), m1, ← hns]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := run_movImm P code (d := 11) (v := 999999999)
    (by decide) cmov q3
  have q4 : u4.pc = after a 7 := by rw [p4, after_after]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_hiReg P code (x := 10) (y := 11) (tB := tr) c78
    (by rw [after_after]; exact hg8) q4
  rw [x4, k4 10 (by decide), u3x10] at p5
  have r15 : Reach P code s u5 := r1.trans (r2.trans (r3.trans (r4.trans r5)))
  have keep5 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → u5.x q = s.x q := fun q h9 h10 h11 => by
    rw [k5, k4 q h11, k3 q h10, k2 q h10, k1 q h9]
  have sp5' : u5.sp = s.sp := by rw [sp5, sp4, sp3, sp2, sp1]
  have io5' : u5.io = s.io := by rw [io5, io4, io3, io2, io1]
  have m5' : u5.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  unfold stampValue
  by_cases hn : 999999999 < ns.toUInt32.toUInt64
  · rw [ite_eq_left hn] at p5
    rw [ite_eq_left hn]
    exact ⟨u5, r15, sp5', m5', io5', fun q h9 h10 h11 _ _ => keep5 q h9 h10 h11, p5⟩
  rw [ite_eq_right hn, after_after] at p5
  rw [ite_eq_right hn]
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_addImm P code (s := u5) (d := 11) (n := 11)
    (imm := 1) (by decide) (by decide) (by rw [p5]; exact c9)
  have u6x11 : u6.x 11 = 1000000000 := by
    rw [x6, k5, x4]
    decide
  have q6 : u6.pc = after a 10 := by rw [p6, p5, ← after_succ]
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := step_subReg P code (s := u6) (d := 12) (n := 31)
    (m := 10) (by decide) (by rw [q6]; exact c10)
  have u7x12 : u7.x 12 = 0 - ns.toUInt32.toUInt64 := by
    rw [x7]
    show 0 - u6.x 10 = _
    rw [k6 10 (by decide), k5, k4 10 (by decide), u3x10]
  have q7 : u7.pc = after a 11 := by rw [p7, q6, ← after_succ]
  obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := step_subImm P code (s := u7) (d := 12) (n := 12)
    (imm := 1) (by decide) (by decide) (by rw [q7]; exact c11)
  have u8x12 : u8.x 12 = 0 - ns.toUInt32.toUInt64 - 1 := by
    rw [x8, u7x12]
    rfl
  have q8 : u8.pc = after a 12 := by rw [p8, q7, ← after_succ]
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := step_udiv P code (s := u8) (d := 12) (n := 12)
    (m := 11) (by decide) (by rw [q8]; exact c12)
  have u9x12 : u9.x 12 = (0 - ns.toUInt32.toUInt64 - 1) / 1000000000 := by
    rw [x9, u8x12, k8 11 (by decide), k7 11 (by decide), u6x11]
  have u9x9 : u9.x 9 = sec := by
    rw [k9 9 (by decide), k8 9 (by decide), k7 9 (by decide), k6 9 (by decide), k5,
      k4 9 (by decide), u3x9]
  have q9 : u9.pc = after a 13 := by rw [p9, q8, ← after_succ]
  obtain ⟨u10, r10, p10, k10, sp10, m10, io10⟩ := run_hiReg P code (x := 9) (y := 12)
    (tB := ov) c1314 (by rw [after_after]; exact hg14) q9
  rw [u9x12, u9x9] at p10
  have r110 : Reach P code s u10 :=
    r15.trans (r6.trans (r7.trans (r8.trans (r9.trans r10))))
  have keep10 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → u10.x q = s.x q :=
    fun q h9 h10 h11 h12 => by
      rw [k10, k9 q h12, k8 q h12, k7 q h12, k6 q h11, keep5 q h9 h10 h11]
  have sp10' : u10.sp = s.sp := by rw [sp10, sp9, sp8, sp7, sp6, sp5']
  have io10' : u10.io = s.io := by rw [io10, io9, io8, io7, io6, io5']
  have m10' : u10.mem = s.mem := by rw [m10, m9, m8, m7, m6, m5']
  by_cases hq : (0 - ns.toUInt32.toUInt64 - 1) / 1000000000 < sec
  · rw [ite_eq_left hq] at p10
    rw [ite_eq_left hq]
    exact ⟨u10, r110, sp10', m10', io10', fun q h9 h10 h11 h12 _ => keep10 q h9 h10 h11 h12, p10⟩
  rw [ite_eq_right hq, after_after] at p10
  rw [ite_eq_right hq]
  obtain ⟨u11, r11, p11, x11, k11, sp11, m11, io11⟩ := step_madd P code (s := u10) (d := d)
    (n := 9) (m := 11) (r := 10) hd (by rw [p10]; exact c15)
  refine ⟨u11, r110.trans r11, by rw [sp11, sp10'], by rw [m11, m10'], by rw [io11, io10'],
    fun q h9 h10 h11 h12 hd' => by rw [k11 q hd', keep10 q h9 h10 h11 h12], by rw [p11, p10,
      ← after_succ], ?_⟩
  rw [x11, k10, k10, k10, k9 9 (by decide), k9 10 (by decide), k9 11 (by decide),
    k8 9 (by decide), k8 10 (by decide), k8 11 (by decide), k7 9 (by decide),
    k7 10 (by decide), k7 11 (by decide), u6x11, k6 9 (by decide), k6 10 (by decide), k5, k5,
    k4 9 (by decide), k4 10 (by decide), u3x9, u3x10]


/-! ## The stub's code -/

/-- The parts of the stub's code at their addresses, with the branch fields that they hold. -/
theorem filestat_code {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) :
    ∃ (gr g11 g14 g8a g14a g8m g14m g8b g14b gt g56 g93 : Fin 524288) (gs ge : Fin 67108864),
      cbField (after (after a 1) 3) tr = .ok gr ∧
      cbField (after (after a 10) 1) (after a 145) = .ok g11 ∧
      cbField (after (after a 10) 4) (after a 145) = .ok g14 ∧
      cbField (after (after a 57) 8) tr = .ok g8a ∧
      cbField (after (after a 57) 14) (after a 137) = .ok g14a ∧
      cbField (after (after a 73) 8) tr = .ok g8m ∧
      cbField (after (after a 73) 14) (after a 137) = .ok g14m ∧
      cbField (after (after a 94) 8) tr = .ok g8b ∧
      cbField (after (after a 94) 14) (after a 137) = .ok g14b ∧
      cbField (after (after a 139) 2) tr = .ok gt ∧ bField (after (after a 139) 4) en = .ok ge ∧
      bField (after a 55) svc = .ok gs ∧ cbField (after a 56) (after a 139) = .ok g56 ∧
      cbField (after a 93) (after a 110) = .ok g93 ∧
      CodeAt code a [.addImm 12 1 64] ∧
      CodeAt code (after a 1) [.ldr 13 17 0, .addImm 13 13 8, .subsReg 31 12 13, .bcond 8 gr] ∧
      CodeAt code (after a 5) (scratchAddr sc) ∧
      CodeAt code (after a 10)
        [.subsImm 31 0 1023, .bcond 8 g11, .addReg 10 20 0, .ldrb 9 10 16, .cbz 9 g14] ∧
      CodeAt code (after a 15) [.orrReg 19 31 30, .orrReg 21 31 1, .strb 31 20 1080] ∧
      CodeAt code (after a 18) (zeroStores 136 32) ∧
      CodeAt code (after a 50) [.addImm 1 20 1080, .movz 2 0x1000 0, .movz 3 0xFFF 0,
        .addImm 4 20 1088, .movz 8 291 0, .bl gs, .cbnz 0 g56] ∧
      CodeAt code (after a 57) (stampCode 144 22 g8a g14a) ∧
      CodeAt code (after a 73) (stampCode 150 23 g8m g14m) ∧
      CodeAt code (after a 89)
        [.ldr 9 20 136, .movz 10 0x800 0, .andReg 9 9 10, .movz 24 0 0, .cbz 9 g93] ∧
      CodeAt code (after a 94) (stampCode 146 24 g8b g14b) ∧
      CodeAt code (after a 110) recordCode ∧
      CodeAt code (after a 139)
        [.subReg 12 31 0, .subsImm 31 12 4095, .bcond 8 gt, .orrReg 0 31 12, .bl ge, .ret 19] ∧
      CodeAt code (after a 145) [.movz 0 8 0, .ret 30] := by
  obtain ⟨range, held, atime, mtime, btime, tail, gs, g56, g93, h1, h2, h3, h4, h5, h6, hs, h56,
    h93, rfl⟩ := filestatStub_ok hg
  obtain ⟨gr, hgr, rfl⟩ := rangeCheck_ok h1
  obtain ⟨g11, g14, hg11, hg14, rfl⟩ := heldTest_ok h2
  obtain ⟨g8a, g14a, hg8a, hg14a, rfl⟩ := stampConvert_ok h3
  obtain ⟨g8m, g14m, hg8m, hg14m, rfl⟩ := stampConvert_ok h4
  obtain ⟨g8b, g14b, hg8b, hg14b, rfl⟩ := stampConvert_ok h5
  obtain ⟨gt, ge, hgt, hge, rfl⟩ := errorTail_ok h6
  simp only [List.append_assoc] at hcode
  have s0 := CodeAt.split code hcode (n := 1) rfl
  have s1 := CodeAt.split code s0.2 (n := 4) rfl
  have s2 := CodeAt.split code s1.2 (n := 5) (by simp [scratchAddr, movImm])
  have s3 := CodeAt.split code s2.2 (n := 5) rfl
  have s4 := CodeAt.split code s3.2 (n := 3) rfl
  have s5 := CodeAt.split code s4.2 (n := 32) (by simp [zeroStores])
  have s6 := CodeAt.split code s5.2 (n := 7) rfl
  have s7 := CodeAt.split code s6.2 (n := 16) (by simp [stampCode, movImm])
  have s8 := CodeAt.split code s7.2 (n := 16) (by simp [stampCode, movImm])
  have s9 := CodeAt.split code s8.2 (n := 5) rfl
  have s10 := CodeAt.split code s9.2 (n := 16) (by simp [stampCode, movImm])
  have s11 := CodeAt.split code s10.2 (n := 29) (by simp [recordCode, strsFrom, movImm])
  have s12 := CodeAt.split code s11.2 (n := 6) rfl
  simp only [after_after, Nat.reduceAdd] at s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12
  exact ⟨gr, g11, g14, g8a, g14a, g8m, g14m, g8b, g14b, gt, g56, g93, gs, ge, hgr, hg11, hg14,
    hg8a, hg14a, hg8m, hg14m, hg8b, hg14b, hgt, hge, hs, h56, h93, s0.1, s1.1, s2.1, s3.1, s4.1,
    s5.1, s6.1, s7.1, s8.1, s9.1, s10.1, s11.1, s12.1, s12.2⟩

/-! ## The stub's front -/

/-- The stub of `fd_filestat_get` from its entry `a`, with the descriptor in X0, the record's
pointer in X1, the area at X17, and the scratch `sc` bytes above it, whose first 1,344 bytes are
Normal memory.  When the record's end, X1 plus 64, exceeds the memory's size, 8 plus the area's
first word, the run reaches the trap stub `tr`.  For a descriptor above 1,023 or whose byte in the
scratch is 0 it returns to X30 with errno 8.  Otherwise it reaches the `BL` of `statx` at
`after a 55` with the descriptor in X0, the path buffer at scratch byte 1,080 in X1, the flags and
the mask in X2 and X3, the record at scratch byte 1,088 in X4, and 291 in X8, the return address
in X19, the scratch in X20, and the record's pointer in X21, after a zero byte at the path buffer
and 32 zero words from the record.  SP, the UART's state, X17, and X18 keep their values. -/
theorem run_filestatFront {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = a) (hsize : ∀ k < 8, P.normal (s.x 17 + UInt64.ofNat k) = true)
    (hscr : ∀ j < 1344, P.normal (s.x 17 + UInt64.ofNat sc + UInt64.ofNat j) = true)
    (hU : P.normal P.uart = false) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if load64 s.mem (s.x 17) + 8 < s.x 1 + 64 then t.pc = tr ∧ t.mem = s.mem
      else if s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0 then
        t.pc = after a 55 ∧ t.x 0 = s.x 0 ∧
          t.x 1 = s.x 17 + UInt64.ofNat sc + UInt64.ofNat 1080 ∧ t.x 2 = 0x1000 ∧
          t.x 3 = 0xFFF ∧ t.x 4 = s.x 17 + UInt64.ofNat sc + UInt64.ofNat 1088 ∧ t.x 8 = 291 ∧
          t.x 19 = s.x 30 ∧ t.x 20 = s.x 17 + UInt64.ofNat sc ∧ t.x 21 = s.x 1 ∧
          t.mem = zeroWords (store8 s.mem (s.x 17 + UInt64.ofNat sc + UInt64.ofNat 1080) 0)
            (s.x 17 + UInt64.ofNat sc + UInt64.ofNat 1088) 32
      else t.pc = s.x 30 ∧ t.x 0 = 8 ∧ t.mem = s.mem := by
  obtain ⟨gr, g11, g14, -, -, -, -, -, -, -, g56, -, gs, -, hgr, hg11, hg14, -, -, -, -, -, -,
    -, -, -, -, -, c0, cR, cS, cH, cP, cZ, cC, -, -, -, -, -, -, cB⟩ := filestat_code code hg hcode
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addImm P code (s := s) (d := 12) (n := 1)
    (imm := 64) (by decide) (by decide) (by rw [hpc]; exact (CodeAt.cons.mp c0).1)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_rangeCheck P code cR hgr q1
    (fun k hk => by rw [k1 17 (by decide)]; exact hsize k hk)
  rw [x1, k1 17 (by decide), m1] at p2
  have keep2 : ∀ q : Fin 32, q ≠ 12 → q ≠ 13 → u2.x q = s.x q := fun q h12 h13 => by
    rw [k2 q h13, k1 q h12]
  have e64 : UInt64.ofNat (64 : Fin 4096).val = 64 := rfl
  rw [e64] at p2
  by_cases hbig : load64 s.mem (s.x 17) + 8 < s.x 1 + 64
  · rw [ite_eq_left hbig] at p2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1], keep2 17 (by decide) (by decide),
      keep2 18 (by decide) (by decide), ?_⟩
    rw [ite_eq_left hbig]
    exact ⟨p2, by rw [m2, m1]⟩
  rw [ite_eq_right hbig] at p2
  simp only [ite_eq_right hbig]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := run_scratchAddr P code cS (s := u2)
    (by rw [p2, after_after])
  have u3x20 : u3.x 20 = s.x 17 + UInt64.ofNat sc := by
    rw [x3, keep2 17 (by decide) (by decide)]
  have u3x0 : u3.x 0 = s.x 0 := by rw [k3 0 (by decide), keep2 0 (by decide) (by decide)]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_heldTest P code (r := 0) (by decide) cH hg11 hg14
    (s := u3) (by rw [p3, after_after])
    (fun h => by
      rw [u3x0] at h
      rw [u3x20, u3x0]
      have hlt : (s.x 0).toNat ≤ 1023 := by
        rw [UInt64.le_iff_toNat_le] at h
        simpa using h
      have e : s.x 17 + UInt64.ofNat sc + s.x 0 + 16 =
          s.x 17 + UInt64.ofNat sc + UInt64.ofNat ((s.x 0).toNat + 16) := by
        rw [UInt64.add_assoc, UInt64.ofNat_add, UInt64.ofNat_toNat]
        rfl
      rw [e]
      exact hscr _ (by omega))
  rw [u3x20, u3x0, m3, m2, m1] at p4
  have keep4 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 12 → q ≠ 13 → q ≠ 20 → u4.x q = s.x q :=
    fun q h9 h10 h12 h13 h20 => by rw [k4 q h9 h10, k3 q h20, keep2 q h12 h13]
  have r14 : Reach P code s u4 := r1.trans (r2.trans (r3.trans r4))
  have sp4' : u4.sp = s.sp := by rw [sp4, sp3, sp2, sp1]
  have io4' : u4.io = s.io := by rw [io4, io3, io2, io1]
  have m4' : u4.mem = s.mem := by rw [m4, m3, m2, m1]
  have u4x20 : u4.x 20 = s.x 17 + UInt64.ofNat sc := by rw [k4 20 (by decide) (by decide), u3x20]
  by_cases hheld : s.x 0 ≤ 1023 ∧ s.mem (s.x 17 + UInt64.ofNat sc + s.x 0 + 16) ≠ 0
  swap
  · rw [ite_eq_right hheld] at p4
    simp only [ite_eq_right hheld]
    obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_movzRet P code cB p4
    refine ⟨u5, r14.trans r5, by rw [sp5, sp4'], by rw [io5, io4'],
      by rw [k5 17 (by decide), keep4 17 (by decide) (by decide) (by decide) (by decide)
        (by decide)],
      by rw [k5 18 (by decide), keep4 18 (by decide) (by decide) (by decide) (by decide)
        (by decide)], ?_, ?_, by rw [m5, m4']⟩
    · rw [p5, keep4 30 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [x5]
      rfl
  rw [ite_eq_left hheld] at p4
  simp only [ite_eq_left hheld]
  have cP0 := (CodeAt.cons.mp cP).1
  have cP1 := (CodeAt.cons.mp (CodeAt.cons.mp cP).2).1
  have cP2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp cP).2).2).1
  simp only [after_after, Nat.reduceAdd] at cP1 cP2
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := step_mov P code (s := u4) (d := 19) (m := 30)
    (by decide) (by rw [p4, after_after]; exact cP0)
  have q5 : u5.pc = after a 16 := by rw [p5, p4, after_after, ← after_succ]
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_mov P code (s := u5) (d := 21) (m := 1)
    (by decide) (by rw [q5]; exact cP1)
  have q6 : u6.pc = after a 17 := by rw [p6, q5, ← after_succ]
  have hpath : u6.x 20 + UInt64.ofNat 1080 = s.x 17 + UInt64.ofNat sc + UInt64.ofNat 1080 := by
    rw [k6 20 (by decide), k5 20 (by decide), u4x20]
  obtain ⟨u7, r7, p7, k7, sp7, io7, m7⟩ := step_strb P code (s := u6) (t := 31) (n := 20)
    (imm := 1080) (k := 1080) (addr := s.x 17 + UInt64.ofNat sc + UInt64.ofNat 1080) (by decide)
    (by rw [q6]; exact cP2) rfl hpath (hscr 1080 (by decide)) hU
  have q7 : u7.pc = after a 18 := by rw [p7, q6, ← after_succ]
  have u7x20 : u7.x 20 = s.x 17 + UInt64.ofNat sc := by
    rw [k7, k6 20 (by decide), k5 20 (by decide), u4x20]
  obtain ⟨u8, r8, p8, k8, sp8, io8, m8⟩ := run_zeroStores P code 32 136 (s := u7) (by decide) cZ q7
    (fun k hk => by
      rw [u7x20]
      exact hscr (8 * 136 + k) (by omega))
  have q8 : u8.pc = after a 50 := by rw [p8, after_after]
  have c := fun k (hk : k < 7) => cC k (by simpa using hk)
  have c0' := c 0 (by omega)
  have c1' := c 1 (by omega)
  have c2' := c 2 (by omega)
  have c3' := c 3 (by omega)
  have c4' := c 4 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, after_zero,
    Nat.reduceAdd] at c0' c1' c2' c3' c4'
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := step_addImm P code (s := u8) (d := 1) (n := 20)
    (imm := 1080) (by decide) (by decide) (by rw [q8]; exact c0')
  have q9 : u9.pc = after a 51 := by rw [p9, q8, ← after_succ]
  obtain ⟨u10, r10, p10, x10, k10, sp10, m10, io10⟩ := run_movz P code (s := u9) (d := 2)
    (v := 0x1000) (by decide) (by rw [q9]; exact c1')
  have q10 : u10.pc = after a 52 := by rw [p10, q9, ← after_succ]
  obtain ⟨u11, r11, p11, x11, k11, sp11, m11, io11⟩ := run_movz P code (s := u10) (d := 3)
    (v := 0xFFF) (by decide) (by rw [q10]; exact c2')
  have q11 : u11.pc = after a 53 := by rw [p11, q10, ← after_succ]
  obtain ⟨u12, r12, p12, x12, k12, sp12, m12, io12⟩ := step_addImm P code (s := u11) (d := 4)
    (n := 20) (imm := 1088) (by decide) (by decide) (by rw [q11]; exact c3')
  have q12 : u12.pc = after a 54 := by rw [p12, q11, ← after_succ]
  obtain ⟨u13, r13, p13, x13, k13, sp13, m13, io13⟩ := run_movz P code (s := u12) (d := 8)
    (v := 291) (by decide) (by rw [q12]; exact c4')
  have keep : ∀ q : Fin 32, q ≠ 1 → q ≠ 2 → q ≠ 3 → q ≠ 4 → q ≠ 8 → q ≠ 19 → q ≠ 21 →
      u13.x q = u4.x q := fun q h1 h2 h3 h4 h8 h19 h21 => by
    rw [k13 q h8, k12 q h4, k11 q h3, k10 q h2, k9 q h1, k8, k7, k6 q h21, k5 q h19]
  have u8x20 : u8.x 20 = s.x 17 + UInt64.ofNat sc := by rw [k8, u7x20]
  refine ⟨u13, r14.trans (r5.trans (r6.trans (r7.trans (r8.trans (r9.trans (r10.trans
    (r11.trans (r12.trans r13)))))))),
    by rw [sp13, sp12, sp11, sp10, sp9, sp8, sp7, sp6, sp5, sp4'],
    by rw [io13, io12, io11, io10, io9, io8, io7, io6, io5, io4'],
    by rw [keep 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), keep4 17 (by decide) (by decide) (by decide) (by decide) (by decide)],
    by rw [keep 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), keep4 18 (by decide) (by decide) (by decide) (by decide) (by decide)],
    by rw [p13, q12, ← after_succ], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), keep4 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [k13 1 (by decide), k12 1 (by decide), k11 1 (by decide), k10 1 (by decide), x9, u8x20]
    rfl
  · rw [k13 2 (by decide), k12 2 (by decide), k11 2 (by decide), x10]
    rfl
  · rw [k13 3 (by decide), k12 3 (by decide), x11]
    rfl
  · rw [k13 4 (by decide), x12, k11 20 (by decide), k10 20 (by decide), k9 20 (by decide), u8x20]
    rfl
  · rw [x13]
    rfl
  · rw [k13 19 (by decide), k12 19 (by decide), k11 19 (by decide), k10 19 (by decide),
      k9 19 (by decide), k8, k7, k6 19 (by decide), x5,
      keep4 30 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [k13 20 (by decide), k12 20 (by decide), k11 20 (by decide), k10 20 (by decide),
      k9 20 (by decide), u8x20]
  · rw [k13 21 (by decide), k12 21 (by decide), k11 21 (by decide), k10 21 (by decide),
      k9 21 (by decide), k8, k7, x6, k5 1 (by decide),
      keep4 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rw [m13, m12, m11, m10, m9, m8, m7, m6, m5, m4', u7x20]
    rfl

/-! ## The stub's stores -/

/-- The memory `m` with the words `ws` stored from `a`, 8 bytes apart. -/
def storedWords (m : UInt64 → UInt8) (a : UInt64) : List UInt64 → UInt64 → UInt8
  | [] => m
  | w :: ws => storedWords (store64 m a w) (a + 8) ws

/-- The stores of `strsFrom base rs` from `a`, with the `8 rs.length` bytes from word `base`
above X13 Normal memory, store the registers `rs` from X13 plus `8 base`, one word each, and
keep every register, SP, and the UART's state. -/
theorem run_strsFrom : ∀ (rs : List (Fin 32)) (base : Nat) {a : UInt64} {s : State},
    base + rs.length ≤ 4096 → CodeAt code a (strsFrom base rs) → s.pc = a →
    (∀ k < 8 * rs.length, P.normal (s.x 13 + UInt64.ofNat (8 * base + k)) = true) →
    ∃ t, Reach P code s t ∧ t.pc = after a rs.length ∧ (∀ q : Fin 32, t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.io = s.io ∧
      t.mem = storedWords s.mem (s.x 13 + UInt64.ofNat (8 * base)) (rs.map s.x)
  | [], _, a, s, _, _, hpc, _ =>
    ⟨s, .refl _, by rw [hpc, List.length_nil, after_zero], fun _ => rfl, rfl, rfl, rfl⟩
  | r :: rs, base, a, s, hb, hcode, hpc, hmap => by
    simp only [List.length_cons] at hb hmap
    have c0 := (CodeAt.cons.mp hcode).1
    have hrest := (CodeAt.cons.mp hcode).2
    have hfin : (Fin.ofNat 4096 base : Fin 4096) = ⟨base, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hfin] at c0
    obtain ⟨u, ru, pu, ku, spu, mu, iou⟩ := step_str P code (s := s) (t := r) (n := 13)
      (i := base) (by omega) (by decide) (by rw [hpc]; exact c0)
      (fun k hk => hmap k (by omega))
    obtain ⟨t, rt, pt, kt, spt, iot, mt⟩ := run_strsFrom rs (base + 1) (s := u) (by omega) hrest
      (by rw [pu, hpc, after_one])
      (fun k hk => by
        rw [ku 13, show 8 * (base + 1) + k = 8 * base + (8 + k) by omega]
        exact hmap (8 + k) (by omega))
    refine ⟨t, ru.trans rt, by rw [pt, after_after, List.length_cons, Nat.add_comm],
      fun q => by rw [kt, ku], by rw [spt, spu], by rw [iot, iou], ?_⟩
    rw [mt, mu, ku 13, List.map_cons, storedWords]
    have e : u.x = s.x := funext ku
    rw [e]
    congr 1
    rw [show 8 * (base + 1) = 8 * base + 8 by omega, ← add_ofNat_add]
    rfl

/-! ## The stub's conversions -/

/-- The conversions of the stub from the `statx` record at `r` in `m`: `none` when a converted
timestamp has nanoseconds above `10^9 − 1`, `some none` when one exceeds the quotient of
`stampValue`, and otherwise the access, modification, and birth times, the last 0 when bit `0x800`
of the record's first word is clear.  The stub converts `stx_atime` at byte 64, `stx_mtime` at
byte 112, and `stx_btime` at byte 80, in that order. -/
def stampsValue (m : UInt64 → UInt8) (r : UInt64) : Option (Option (UInt64 × UInt64 × UInt64)) :=
  match stampValue (load64 m (r + UInt64.ofNat 64)) (load64 m (r + UInt64.ofNat 72)) with
  | none => none
  | some none => some none
  | some (some ta) =>
    match stampValue (load64 m (r + UInt64.ofNat 112)) (load64 m (r + UInt64.ofNat 120)) with
    | none => none
    | some none => some none
    | some (some tm) =>
      if load64 m r &&& 2048 = 0 then some (some (ta, tm, 0))
      else
        match stampValue (load64 m (r + UInt64.ofNat 80)) (load64 m (r + UInt64.ofNat 88)) with
        | none => none
        | some none => some none
        | some (some tb) => some (some (ta, tm, tb))

/-- The stub's conversions from `after a 57`, with the scratch at X20, whose `statx` record's 256
bytes from byte 1,088 are Normal memory: the trap stub `tr`, the return to X19 with errno 61, or
`after a 110` with the three times in X22 to X24, as `stampsValue` states.  The memory, SP, and the
UART's state keep their values, and every register but X0, X9 to X12, and X22 to X24. -/
theorem run_filestatStamps {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 57)
    (hrec : ∀ k < 256, P.normal (s.x 20 + UInt64.ofNat (1088 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.mem = s.mem ∧
      (∀ q : Fin 32, q ≠ 0 → q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 22 → q ≠ 23 → q ≠ 24 →
        t.x q = s.x q) ∧
      match stampsValue s.mem (s.x 20 + UInt64.ofNat 1088) with
      | none => t.pc = tr
      | some none => t.pc = s.x 19 ∧ t.x 0 = 61
      | some (some (ta, tm, tb)) =>
        t.pc = after a 110 ∧ t.x 22 = ta ∧ t.x 23 = tm ∧ t.x 24 = tb := by
  obtain ⟨_gr, _g11, _g14, g8a, g14a, g8m, g14m, g8b, g14b, _gt, _g56, g93, _gs, _ge, -, -, -,
    hg8a, hg14a, hg8m, hg14m, hg8b, hg14b, -, -, -, -, h93, -, -, -, -, -, -, -, cA, cM, cK, cBt,
    cRec, -, -⟩ := filestat_code code hg hcode
  have cOv : CodeAt code (after a 137) [.movz 0 61 0, .ret 19] := by
    simpa [recordCode, strsFrom, movImm, after_after] using
      CodeAt.drop_take code cRec 27 2 (by simp [recordCode, strsFrom, movImm])
  have cOv0 := (CodeAt.cons.mp cOv).1
  have cOv1 := (CodeAt.cons.mp (CodeAt.cons.mp cOv).2).1
  simp only [after_after, Nat.reduceAdd] at cOv1
  -- the return of errno 61 from a state at `after a 137`
  have ov : ∀ u : State, u.pc = after a 137 → ∃ t, Reach P code u t ∧ t.pc = u.x 19 ∧
      t.x 0 = 61 ∧ (∀ q : Fin 32, q ≠ 0 → t.x q = u.x q) ∧ t.sp = u.sp ∧ t.mem = u.mem ∧
      t.io = u.io := by
    intro u hu
    obtain ⟨v1, rv1, pv1, xv1, kv1, spv1, mv1, iov1⟩ := run_movz P code (s := u) (d := 0)
      (v := 61) (by decide) (by rw [hu]; exact cOv0)
    obtain ⟨v2, rv2, pv2, kv2, spv2, mv2, iov2⟩ := step_ret P code (s := v1) (n := 19)
      (by rw [pv1, hu, ← after_succ]; exact cOv1)
    exact ⟨v2, rv1.trans rv2, by rw [pv2, kv1 19 (by decide)], by rw [kv2, xv1]; rfl,
      fun q hq => by rw [kv2, kv1 q hq], by rw [spv2, spv1], by rw [mv2, mv1], by rw [iov2, iov1]⟩
  have hmapAt : ∀ (off : Fin 4096) (j : Nat), 8 * off.val = 1088 + j → j + 16 ≤ 256 →
      ∀ k < 16, P.normal (s.x 20 + UInt64.ofNat (8 * off.val + k)) = true := by
    intro off j hj hjk k hk
    rw [hj, show 1088 + j + k = 1088 + (j + k) by omega]
    exact hrec (j + k) (by omega)
  have eAt : ∀ (off : Fin 4096) (j : Nat), 8 * off.val = 1088 + j →
      s.x 20 + UInt64.ofNat 1088 + UInt64.ofNat j = s.x 20 + UInt64.ofNat (8 * off.val) := by
    intro off j hj
    rw [add_ofNat_add, hj]
  obtain ⟨t1, r1, sp1, m1, io1, k1, h1⟩ := run_stampConvert P code (d := 22) (by decide)
    (by decide) cA hg8a hg14a hpc (hmapAt 144 64 rfl (by decide))
  unfold stampsValue
  rw [eAt 144 64 rfl, eAt 145 72 rfl, eAt 150 112 rfl, eAt 151 120 rfl, eAt 146 80 rfl,
    eAt 147 88 rfl]
  have e145 : 8 * ((144 : Fin 4096).val + 1) = 8 * (145 : Fin 4096).val := rfl
  rw [e145] at h1
  rcases hA : stampValue (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (144 : Fin 4096).val)))
    (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (145 : Fin 4096).val))) with _ | _ | ta
  · rw [hA] at h1
    exact ⟨t1, r1, sp1, io1, m1, fun q _ h9 h10 h11 h12 h22 _ _ => k1 q h9 h10 h11 h12 h22, h1⟩
  · rw [hA] at h1
    obtain ⟨t2, r2, p2, x2, k2, sp2, m2, io2⟩ := ov t1 h1
    refine ⟨t2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1], by rw [m2, m1],
      fun q h0 h9 h10 h11 h12 h22 _ _ => by rw [k2 q h0, k1 q h9 h10 h11 h12 h22], ?_, x2⟩
    rw [p2, k1 19 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [hA] at h1
  obtain ⟨p1, x1⟩ := h1
  obtain ⟨t2, r2, sp2, m2, io2, k2, h2⟩ := run_stampConvert P code (d := 23) (s := t1)
    (by decide) (by decide) cM hg8m hg14m (by rw [p1, after_after])
    (fun k hk => by
      rw [k1 20 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hmapAt 150 112 rfl (by decide) k hk)
  have e151 : 8 * ((150 : Fin 4096).val + 1) = 8 * (151 : Fin 4096).val := rfl
  rw [e151, k1 20 (by decide) (by decide) (by decide) (by decide) (by decide), m1] at h2
  have keep2 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 22 → q ≠ 23 →
      t2.x q = s.x q := fun q h9 h10 h11 h12 h22 h23 => by
    rw [k2 q h9 h10 h11 h12 h23, k1 q h9 h10 h11 h12 h22]
  rcases hM : stampValue (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (150 : Fin 4096).val)))
    (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (151 : Fin 4096).val))) with _ | _ | tm
  · rw [hM] at h2
    exact ⟨t2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1], by rw [m2, m1],
      fun q _ h9 h10 h11 h12 h22 h23 _ => keep2 q h9 h10 h11 h12 h22 h23, h2⟩
  · rw [hM] at h2
    obtain ⟨t3, r3, p3, x3, k3, sp3, m3, io3⟩ := ov t2 h2
    refine ⟨t3, r1.trans (r2.trans r3), by rw [sp3, sp2, sp1], by rw [io3, io2, io1],
      by rw [m3, m2, m1],
      fun q h0 h9 h10 h11 h12 h22 h23 _ => by rw [k3 q h0, keep2 q h9 h10 h11 h12 h22 h23], ?_,
      x3⟩
    rw [p3, keep2 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [hM] at h2
  obtain ⟨p2, x2⟩ := h2
  have t2x22 : t2.x 22 = ta := by
    rw [k2 22 (by decide) (by decide) (by decide) (by decide) (by decide), x1]
  -- the mask
  have cK0 := (CodeAt.cons.mp cK).1
  have cK1 := (CodeAt.cons.mp (CodeAt.cons.mp cK).2).1
  have cK2 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp cK).2).2).1
  have cK3 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp cK).2).2).2).1
  have cK4 := (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp (CodeAt.cons.mp
    (CodeAt.cons.mp cK).2).2).2).2).1
  simp only [after_after, Nat.reduceAdd] at cK1 cK2 cK3 cK4
  have q2 : t2.pc = after a 89 := by rw [p2, after_after]
  obtain ⟨u1, ru1, pu1, xu1, ku1, spu1, mu1, iou1⟩ := step_ldr P code (s := t2) (t := 9)
    (n := 20) (i := 136) (by decide) (by decide) (by decide) (by rw [q2]; exact cK0)
    (fun k hk => by
      rw [keep2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hrec k (by omega))
  have qu1 : u1.pc = after a 90 := by rw [pu1, q2, ← after_succ]
  obtain ⟨u2, ru2, pu2, xu2, ku2, spu2, mu2, iou2⟩ := run_movz P code (s := u1) (d := 10)
    (v := 0x800) (by decide) (by rw [qu1]; exact cK1)
  have qu2 : u2.pc = after a 91 := by rw [pu2, qu1, ← after_succ]
  obtain ⟨u3, ru3, pu3, xu3, ku3, spu3, mu3, iou3⟩ := step_setX P code (s := u2) (d := 9)
    (v := u2.x 9 &&& u2.x 10) (by decide) (by rw [qu2]; exact cK2) rfl
  have qu3 : u3.pc = after a 92 := by rw [pu3, qu2, ← after_succ]
  obtain ⟨u4, ru4, pu4, xu4, ku4, spu4, mu4, iou4⟩ := run_movz P code (s := u3) (d := 24)
    (v := 0) (by decide) (by rw [qu3]; exact cK3)
  have qu4 : u4.pc = after a 93 := by rw [pu4, qu3, ← after_succ]
  obtain ⟨u5, ru5, pu5, ku5, spu5, mu5, iou5⟩ := step_cbz P code (s := u4) (r := 9)
    (target := after a 110) (by rw [qu4]; exact cK4) (by rw [qu4]; exact cbField_target h93)
  have hmask : u4.x 9 = load64 s.mem (s.x 20 + UInt64.ofNat 1088) &&& 2048 := by
    rw [ku4 9 (by decide), xu3, xu2, ku2 9 (by decide), xu1,
      keep2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), m2, m1]
    rfl
  rw [hmask] at pu5
  have mem5 : u5.mem = s.mem := by rw [mu5, mu4, mu3, mu2, mu1, m2, m1]
  have sp5 : u5.sp = s.sp := by rw [spu5, spu4, spu3, spu2, spu1, sp2, sp1]
  have io5 : u5.io = s.io := by rw [iou5, iou4, iou3, iou2, iou1, io2, io1]
  have keep5 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 22 → q ≠ 23 → q ≠ 24 →
      u5.x q = s.x q := fun q h9 h10 h11 h12 h22 h23 h24 => by
    rw [ku5, ku4 q h24, ku3 q h9, ku2 q h10, ku1 q h9, keep2 q h9 h10 h11 h12 h22 h23]
  have u5x22 : u5.x 22 = ta := by
    rw [ku5, ku4 22 (by decide), ku3 22 (by decide), ku2 22 (by decide), ku1 22 (by decide),
      t2x22]
  have u5x23 : u5.x 23 = tm := by
    rw [ku5, ku4 23 (by decide), ku3 23 (by decide), ku2 23 (by decide), ku1 23 (by decide), x2]
  have r5 : Reach P code s u5 :=
    r1.trans (r2.trans (ru1.trans (ru2.trans (ru3.trans (ru4.trans ru5)))))
  by_cases hz : load64 s.mem (s.x 20 + UInt64.ofNat 1088) &&& 2048 = 0
  · rw [ite_eq_left hz] at pu5
    simp only [ite_eq_left hz]
    refine ⟨u5, r5, sp5, io5, mem5, fun q _ h9 h10 h11 h12 h22 h23 h24 =>
      keep5 q h9 h10 h11 h12 h22 h23 h24, pu5, u5x22, u5x23, ?_⟩
    rw [ku5, xu4]
    rfl
  rw [ite_eq_right hz, qu4, ← after_succ] at pu5
  simp only [ite_eq_right hz]
  obtain ⟨t3, r3, sp3, m3, io3, k3, h3⟩ := run_stampConvert P code (d := 24) (s := u5)
    (by decide) (by decide) cBt hg8b hg14b pu5
    (fun k hk => by
      rw [keep5 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]
      exact hmapAt 146 80 rfl (by decide) k hk)
  have e147 : 8 * ((146 : Fin 4096).val + 1) = 8 * (147 : Fin 4096).val := rfl
  rw [e147, keep5 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), mem5] at h3
  have keep3 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 22 → q ≠ 23 → q ≠ 24 →
      t3.x q = s.x q := fun q h9 h10 h11 h12 h22 h23 h24 => by
    rw [k3 q h9 h10 h11 h12 h24, keep5 q h9 h10 h11 h12 h22 h23 h24]
  rcases hB : stampValue (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (146 : Fin 4096).val)))
    (load64 s.mem (s.x 20 + UInt64.ofNat (8 * (147 : Fin 4096).val))) with _ | _ | tb
  · rw [hB] at h3
    exact ⟨t3, r5.trans r3, by rw [sp3, sp5], by rw [io3, io5], by rw [m3, mem5],
      fun q _ h9 h10 h11 h12 h22 h23 h24 => keep3 q h9 h10 h11 h12 h22 h23 h24, h3⟩
  · rw [hB] at h3
    obtain ⟨t4, r4, p4, x4, k4, sp4, m4, io4⟩ := ov t3 h3
    refine ⟨t4, r5.trans (r3.trans r4), by rw [sp4, sp3, sp5], by rw [io4, io3, io5],
      by rw [m4, m3, mem5],
      fun q h0 h9 h10 h11 h12 h22 h23 h24 => by rw [k4 q h0, keep3 q h9 h10 h11 h12 h22 h23 h24],
      ?_, x4⟩
    rw [p4, keep3 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  rw [hB] at h3
  obtain ⟨p3, x3⟩ := h3
  refine ⟨t3, r5.trans r3, by rw [sp3, sp5], by rw [io3, io5], by rw [m3, mem5],
    fun q _ h9 h10 h11 h12 h22 h23 h24 => keep3 q h9 h10 h11 h12 h22 h23 h24,
    by rw [p3, after_after], ?_, ?_, x3⟩
  · rw [k3 22 (by decide) (by decide) (by decide) (by decide) (by decide), u5x22]
  · rw [k3 23 (by decide) (by decide) (by decide) (by decide) (by decide), u5x23]

/-! ## The stub's record -/

/-- The file type that the stub finds for the byte `b`, byte 29 of the `statx` record, whose high
half holds the bits `S_IFMT` of `stx_mode`: the four bits of `filetypeTable` from four times
that half. -/
def fileTypeOf (b : UInt8) : UInt64 :=
  (filetypeTable >>> ((b.toUInt64 >>> 4 + b.toUInt64 >>> 4 + (b.toUInt64 >>> 4 + b.toUInt64 >>> 4))
    % 64)) &&& 15

/-- The eight words of `filestat` that the stub stores, from the `statx` record at `r` in `m`
and the times `ta`, `tm`, and `tb`: 1, `stx_ino`, the file type, `stx_nlink`, `stx_size`, and
the times. -/
def filestatWords (m : UInt64 → UInt8) (r ta tm tb : UInt64) : List UInt64 :=
  [1, load64 m (r + UInt64.ofNat 32), fileTypeOf (m (r + UInt64.ofNat 29)),
    (load64 m (r + UInt64.ofNat 16)).toUInt32.toUInt64, load64 m (r + UInt64.ofNat 40), ta, tm,
    tb]

/-- The stub's record from `after a 110`, with the scratch at X20, whose `statx` record's 256 bytes
from byte 1,088 are Normal memory, the record's pointer in X21, whose 64 bytes at the guest's
address X17 + X21 + 4096 are Normal memory, and the three times in X22 to X24: the eight words of
`filestatWords` stored at the guest's address and the return to X19 with errno 0.  SP, the UART's
state, X17, and X18 keep their values. -/
theorem run_filestatRecord {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) (hcode : CodeAt code a is) {s : State}
    (hpc : s.pc = after a 110)
    (hrec : ∀ k < 256, P.normal (s.x 20 + UInt64.ofNat (1088 + k)) = true)
    (hout : ∀ k < 64, P.normal (s.x 17 + s.x 21 + UInt64.ofNat (4096 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      t.pc = s.x 19 ∧ t.x 0 = 0 ∧
      t.mem = storedWords s.mem (s.x 17 + s.x 21 + UInt64.ofNat 4096)
        (filestatWords s.mem (s.x 20 + UInt64.ofNat 1088) (s.x 22) (s.x 23) (s.x 24)) := by
  obtain ⟨_gr, _g11, _g14, _g8a, _g14a, _g8m, _g14m, _g8b, _g14b, _gt, _g56, _g93, _gs, _ge, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, cRec, -, -⟩ :=
    filestat_code code hg hcode
  simp only [recordCode, List.append_assoc] at cRec
  have cr := CodeAt.split code cRec (n := 4) rfl
  have cr2 := CodeAt.split code cr.2 (n := 4) (by simp [movImm])
  have cr3 := CodeAt.split code cr2.2 (n := 9) rfl
  have cr4 := CodeAt.split code cr3.2 (n := 8) (by simp [strsFrom])
  simp only [after_after, Nat.reduceAdd] at cr2 cr3 cr4
  have c := fun k (hk : k < 4) => cr.1 k (by simpa using hk)
  have d := fun k (hk : k < 9) => cr3.1 k (by simpa using hk)
  have e := fun k (hk : k < 4) => cr4.2 k (by simpa using hk)
  have c0 := c 0 (by omega)
  have c1 := c 1 (by omega)
  have c2 := c 2 (by omega)
  have c3 := c 3 (by omega)
  have d0 := d 0 (by omega)
  have d1 := d 1 (by omega)
  have d2 := d 2 (by omega)
  have d3 := d 3 (by omega)
  have d4 := d 4 (by omega)
  have d5 := d 5 (by omega)
  have d6 := d 6 (by omega)
  have d7 := d 7 (by omega)
  have d8 := d 8 (by omega)
  have e0 := e 0 (by omega)
  have e1 := e 1 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, after_zero,
    Nat.reduceAdd] at c0 c1 c2 c3 d0 d1 d2 d3 d4 d5 d6 d7 d8 e0 e1
  have hld : ∀ (i j : Nat), 8 * i = 1088 + j → j + 8 ≤ 256 → ∀ k < 8,
      P.normal (s.x 20 + UInt64.ofNat (8 * i + k)) = true := by
    intro i j hij hj k hk
    rw [hij, show 1088 + j + k = 1088 + (j + k) by omega]
    exact hrec (j + k) (by omega)
  have h1117 : P.normal (s.x 20 + UInt64.ofNat (1117 : Fin 4096).val) = true := hrec 29 (by omega)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_setX P code (s := s) (d := 10) (by decide)
    (by rw [hpc]; exact c0) (exec_ldrb_base P (t := 10) (by decide) h1117)
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_lsrImm P code (s := u1) (d := 10) (n := 10)
    (sh := 4) (k := 4) (by decide) (by rw [p1, hpc, ← after_succ]; exact c1) rfl
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addReg P code (s := u2) (d := 10) (n := 10)
    (m := 10) (by decide) (by rw [p2, p1, hpc, ← after_succ, ← after_succ]; exact c2)
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_addReg P code (s := u3) (d := 10) (n := 10)
    (m := 10) (by decide)
    (by rw [p3, p2, p1, hpc, ← after_succ, ← after_succ, ← after_succ]; exact c3)
  have q4 : u4.pc = after a 114 := by
    rw [p4, p3, p2, p1, hpc, ← after_succ, ← after_succ, ← after_succ, ← after_succ]
  obtain ⟨u5, r5, p5, x5, k5, sp5, m5, io5⟩ := run_movImm P code (d := 11) (v := filetypeTable)
    (by decide) cr2.1 q4
  have q5 : u5.pc = after a 118 := by rw [p5, after_after]
  obtain ⟨u6, r6, p6, x6, k6, sp6, m6, io6⟩ := step_setX P code (s := u5) (d := 11)
    (v := u5.x 11 >>> (u5.x 10 % 64)) (by decide) (by rw [q5]; exact d0) rfl
  have q6 : u6.pc = after a 119 := by rw [p6, q5, ← after_succ]
  obtain ⟨u7, r7, p7, x7, k7, sp7, m7, io7⟩ := run_movz P code (s := u6) (d := 12) (v := 0xF)
    (by decide) (by rw [q6]; exact d1)
  have q7 : u7.pc = after a 120 := by rw [p7, q6, ← after_succ]
  obtain ⟨u8, r8, p8, x8, k8, sp8, m8, io8⟩ := step_setX P code (s := u7) (d := 11)
    (v := u7.x 11 &&& u7.x 12) (by decide) (by rw [q7]; exact d2) rfl
  have q8 : u8.pc = after a 121 := by rw [p8, q7, ← after_succ]
  have u8x20 : u8.x 20 = s.x 20 := by
    rw [k8 20 (by decide), k7 20 (by decide), k6 20 (by decide), k5 20 (by decide),
      k4 20 (by decide), k3 20 (by decide), k2 20 (by decide), k1 20 (by decide)]
  have u8mem : u8.mem = s.mem := by rw [m8, m7, m6, m5, m4, m3, m2, m1]
  obtain ⟨u9, r9, p9, x9, k9, sp9, m9, io9⟩ := step_ldr P code (s := u8) (t := 25) (n := 20)
    (i := 140) (by decide) (by decide) (by decide) (by rw [q8]; exact d3)
    (by rw [u8x20]; exact hld 140 32 rfl (by decide))
  have q9 : u9.pc = after a 122 := by rw [p9, q8, ← after_succ]
  obtain ⟨u10, r10, p10, x10, k10, sp10, m10, io10⟩ := step_ldr P code (s := u9) (t := 26)
    (n := 20) (i := 138) (by decide) (by decide) (by decide) (by rw [q9]; exact d4)
    (by rw [k9 20 (by decide), u8x20]; exact hld 138 16 rfl (by decide))
  have q10 : u10.pc = after a 123 := by rw [p10, q9, ← after_succ]
  obtain ⟨u11, r11, p11, x11, k11, sp11, m11, io11⟩ := step_orrW P code (s := u10) (d := 26)
    (n := 26) (by decide) (by rw [q10]; exact d5)
  have q11 : u11.pc = after a 124 := by rw [p11, q10, ← after_succ]
  obtain ⟨u12, r12, p12, x12, k12, sp12, m12, io12⟩ := step_ldr P code (s := u11) (t := 27)
    (n := 20) (i := 141) (by decide) (by decide) (by decide) (by rw [q11]; exact d6)
    (by
      rw [k11 20 (by decide), k10 20 (by decide), k9 20 (by decide), u8x20]
      exact hld 141 40 rfl (by decide))
  have q12 : u12.pc = after a 125 := by rw [p12, q11, ← after_succ]
  obtain ⟨u13, r13, p13, x13, k13, sp13, m13, io13⟩ := step_addReg P code (s := u12) (d := 13)
    (n := 17) (m := 21) (by decide) (by rw [q12]; exact d7)
  have q13 : u13.pc = after a 126 := by rw [p13, q12, ← after_succ]
  obtain ⟨u14, r14, p14, x14, k14, sp14, m14, io14⟩ := run_movz P code (s := u13) (d := 9)
    (v := 1) (by decide) (by rw [q13]; exact d8)
  have q14 : u14.pc = after a 127 := by rw [p14, q13, ← after_succ]
  have keep14 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → q ≠ 25 → q ≠ 26 →
      q ≠ 27 → u14.x q = s.x q := fun q h9 h10 h11 h12 h13 h25 h26 h27 => by
    rw [k14 q h9, k13 q h13, k12 q h27, k11 q h26, k10 q h26, k9 q h25, k8 q h11, k7 q h12,
      k6 q h11, k5 q h11, k4 q h10, k3 q h10, k2 q h10, k1 q h10]
  have u14x13 : u14.x 13 = s.x 17 + s.x 21 := by
    rw [k14 13 (by decide), x13, k12 17 (by decide), k11 17 (by decide), k10 17 (by decide),
      k9 17 (by decide), k12 21 (by decide), k11 21 (by decide), k10 21 (by decide),
      k9 21 (by decide)]
    rw [k8 17 (by decide), k7 17 (by decide), k6 17 (by decide), k5 17 (by decide),
      k4 17 (by decide), k3 17 (by decide), k2 17 (by decide), k1 17 (by decide),
      k8 21 (by decide), k7 21 (by decide), k6 21 (by decide), k5 21 (by decide),
      k4 21 (by decide), k3 21 (by decide), k2 21 (by decide), k1 21 (by decide)]
  have u14mem : u14.mem = s.mem := by rw [m14, m13, m12, m11, m10, m9, u8mem]
  obtain ⟨u15, r15, p15, k15, sp15, io15, m15⟩ :=
    run_strsFrom P code [9, 25, 11, 26, 27, 22, 23, 24] 512 (s := u14) (by decide) cr4.1 q14
    (fun k hk => by
      rw [u14x13, show 8 * 512 + k = 4096 + k by omega]
      exact hout k (by simpa using hk))
  have q15 : u15.pc = after a 135 := by rw [p15, after_after]; rfl
  obtain ⟨u16, r16, p16, x16, k16, sp16, m16, io16⟩ := run_movz P code (s := u15) (d := 0)
    (v := 0) (by decide) (by rw [q15]; exact e0)
  obtain ⟨u17, r17, p17, k17, sp17, m17, io17⟩ := step_ret P code (s := u16) (n := 19)
    (by rw [p16, q15, ← after_succ]; exact e1)
  refine ⟨u17, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans (r8.trans
    (r9.trans (r10.trans (r11.trans (r12.trans (r13.trans (r14.trans (r15.trans (r16.trans
    r17))))))))))))))),
    by rw [sp17, sp16, sp15, sp14, sp13, sp12, sp11, sp10, sp9, sp8, sp7, sp6, sp5, sp4, sp3, sp2,
      sp1],
    by rw [io17, io16, io15, io14, io13, io12, io11, io10, io9, io8, io7, io6, io5, io4, io3, io2,
      io1],
    by rw [k17, k16 17 (by decide), k15, keep14 17 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)],
    by rw [k17, k16 18 (by decide), k15, keep14 18 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)],
    by rw [p17, k16 19 (by decide), k15, keep14 19 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)],
    by rw [k17, x16]; rfl, ?_⟩
  have ea : ∀ j : Nat, s.x 20 + UInt64.ofNat 1088 + UInt64.ofNat j =
      s.x 20 + UInt64.ofNat (1088 + j) := fun j => add_ofNat_add _ _ _
  have v9 : u14.x 9 = 1 := by rw [x14]; rfl
  have v25 : u14.x 25 = load64 s.mem (s.x 20 + UInt64.ofNat 1088 + UInt64.ofNat 32) := by
    rw [k14 25 (by decide), k13 25 (by decide), k12 25 (by decide), k11 25 (by decide),
      k10 25 (by decide), x9, u8x20, u8mem, ea]
  have v11 : u14.x 11 = fileTypeOf (s.mem (s.x 20 + UInt64.ofNat 1088 + UInt64.ofNat 29)) := by
    rw [k14 11 (by decide), k13 11 (by decide), k12 11 (by decide), k11 11 (by decide),
      k10 11 (by decide), k9 11 (by decide), x8, k7 11 (by decide), x7, x6, k5 10 (by decide), x5,
      x4, x3, x2, x1, ea]
    rfl
  have v26 : u14.x 26 =
      (load64 s.mem (s.x 20 + UInt64.ofNat 1088 + UInt64.ofNat 16)).toUInt32.toUInt64 := by
    rw [k14 26 (by decide), k13 26 (by decide), k12 26 (by decide), x11, x10, k9 20 (by decide),
      u8x20, m9, u8mem, ea]
  have v27 : u14.x 27 = load64 s.mem (s.x 20 + UInt64.ofNat 1088 + UInt64.ofNat 40) := by
    rw [k14 27 (by decide), k13 27 (by decide), x12, k11 20 (by decide), k10 20 (by decide),
      k9 20 (by decide), u8x20, m11, m10, m9, u8mem, ea]
  rw [m17, m16, m15, u14mem, u14x13]
  simp only [List.map_cons, List.map_nil, filestatWords]
  rw [v9, v25, v11, v26, v27,
    keep14 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    keep14 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    keep14 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]

/-! ## The stub's back -/

/-- The stub of `fd_filestat_get` from the result of its call in X0 at `after a 56`, with the
scratch at X20, whose `statx` record's 256 bytes are Normal memory, the record's pointer in X21,
whose 64 bytes at the guest's address are Normal memory, and the return address in X19.  A result
other than 0 reaches the error tail: the return of the errno of a negated error number, or the
trap stub `tr`, with the memory kept.  For 0 the run reaches the trap stub, the return of errno 61
with the memory kept, or the return of errno 0 with the eight words of `filestatWords` stored at
the guest's address, as `stampsValue` states.  SP, the UART's state, X17, and X18 keep their
values. -/
theorem run_filestatBack {a svc tr en : UInt64} {sc : Nat} {is : List Instr}
    (hg : filestatStub a svc tr en sc = .ok is) (hcode : CodeAt code a is)
    (hen : CodeAt code en errnoRoutine) {s : State} (hpc : s.pc = after a 56)
    (hrec : ∀ k < 256, P.normal (s.x 20 + UInt64.ofNat (1088 + k)) = true)
    (hout : ∀ k < 64, P.normal (s.x 17 + s.x 21 + UInt64.ofNat (4096 + k)) = true) :
    ∃ t, Reach P code s t ∧ t.sp = s.sp ∧ t.io = s.io ∧ t.x 17 = s.x 17 ∧ t.x 18 = s.x 18 ∧
      if s.x 0 ≠ 0 then t.mem = s.mem ∧
        (if 0 - s.x 0 ≤ 4095 then t.pc = s.x 19 ∧ t.x 0 = errnoLookup errnoTable (0 - s.x 0)
          else t.pc = tr)
      else match stampsValue s.mem (s.x 20 + UInt64.ofNat 1088) with
        | none => t.pc = tr ∧ t.mem = s.mem
        | some none => t.pc = s.x 19 ∧ t.x 0 = 61 ∧ t.mem = s.mem
        | some (some (ta, tm, tb)) => t.pc = s.x 19 ∧ t.x 0 = 0 ∧
          t.mem = storedWords s.mem (s.x 17 + s.x 21 + UInt64.ofNat 4096)
            (filestatWords s.mem (s.x 20 + UInt64.ofNat 1088) ta tm tb) := by
  obtain ⟨_gr, _g11, _g14, _g8a, _g14a, _g8m, _g14m, _g8b, _g14b, gt, g56, _g93, gs, ge, -, -, -,
    -, -, -, -, -, -, hgt, hge, -, h56, -, -, -, -, -, -, -, cC, -, -, -, -, -, cT, -⟩ :=
    filestat_code code hg hcode
  have c56 := cC 6 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_after, Nat.reduceAdd] at c56
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbnz P code (s := s) (target := after a 139)
    (by rw [hpc]; exact c56) (by rw [hpc]; exact cbField_target h56)
  by_cases h0 : s.x 0 ≠ 0
  · rw [ite_eq_left h0] at p1
    obtain ⟨u2, r2, sp2, m2, io2, k2, hc2⟩ := run_errorTail P code cT hgt hge hen p1
    rw [k1 0, k1 19] at hc2
    refine ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      by rw [k2 17 (by decide) (by decide) (by decide), k1],
      by rw [k2 18 (by decide) (by decide) (by decide), k1], ?_⟩
    rw [ite_eq_left h0]
    exact ⟨by rw [m2, m1], hc2⟩
  rw [ite_eq_right h0, hpc, ← after_succ] at p1
  have hz : s.x 0 = 0 := Classical.not_not.mp h0
  obtain ⟨u2, r2, sp2, io2, m2, k2, h2⟩ := run_filestatStamps P code hg hcode (s := u1) p1
    (fun k hk => by rw [k1]; exact hrec k hk)
  rw [k1 20, m1, k1 19] at h2
  simp only [ite_eq_right h0]
  rcases hS : stampsValue s.mem (s.x 20 + UInt64.ofNat 1088) with _ | _ | ⟨ta, tm, tb⟩
  · rw [hS] at h2
    exact ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      by rw [k2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), k1],
      by rw [k2 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), k1], h2, by rw [m2, m1]⟩
  · rw [hS] at h2
    exact ⟨u2, r1.trans r2, by rw [sp2, sp1], by rw [io2, io1],
      by rw [k2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), k1],
      by rw [k2 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), k1], h2.1, h2.2, by rw [m2, m1]⟩
  rw [hS] at h2
  obtain ⟨p2, x22, x23, x24⟩ := h2
  have keep2 : ∀ q : Fin 32, q ≠ 0 → q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 22 → q ≠ 23 →
      q ≠ 24 → u2.x q = s.x q := fun q h0 h9 h10 h11 h12 h22 h23 h24 => by
    rw [k2 q h0 h9 h10 h11 h12 h22 h23 h24, k1]
  obtain ⟨t, rt, spt, iot, x17t, x18t, pt, x0t, mt⟩ := run_filestatRecord P code hg hcode
    (s := u2) p2
    (fun k hk => by
      rw [keep2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      exact hrec k hk)
    (fun k hk => by
      rw [keep2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), keep2 21 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)]
      exact hout k hk)
  have e20 := keep2 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have e17 := keep2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have e21 := keep2 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have e18 := keep2 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have e19 := keep2 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  rw [e20, e17, e21, x22, x23, x24, m2, m1] at mt
  exact ⟨t, r1.trans (r2.trans rt), by rw [spt, sp2, sp1], by rw [iot, io2, io1],
    by rw [x17t, e17], by rw [x18t, e18], by rw [pt, e19], x0t, mt⟩

end Runs

end LeanExe.A64
