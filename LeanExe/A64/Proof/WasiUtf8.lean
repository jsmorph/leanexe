import LeanExe.A64.Proof.WasiStubs
import LeanExe.A64.WasiFiles

/-!
The run of `utf8Check` of `LeanExe/A64/WasiFiles.lean` in the program's model.  `run_utf8Check`
follows the check from its first word over the `n` bytes from the guest's address
`X17 + 4096 + X2`, with `n` in X3, to the next word after it when `utf8Scan` accepts the bytes and
to `bad` otherwise, and it changes no register outside X9 to X13 and neither SP, the memory, nor
the UART's state.  The proof is an induction on the number of bytes that remain at the loop's
head, where X9 holds the address of the next byte and X10 the count that remains.

`run_utf8Step` follows one pass from the head through the tests of a character's first byte and
the run of its class, `run_utf8Two`, `run_utf8Three`, or `run_utf8Four`, to the head with X9 and
X10 moved past the character or to the end of the loop (`Utf8Pass`).  The decision of each pass
is that of `utf8Scan` on the character's bytes, which `utf8Scan_one` to `utf8Scan_short4` state
in terms of the bytes' values.  The tests of a continuation byte subtract `0x80` and compare the
difference with `0x40` (`cont_test`), and the tests of a three-byte or four-byte character's
second byte depend on its first (`run_neLo`, `run_neHs`).
-/

namespace LeanExe.A64

/-! ## The generator -/

theorem bind_eq_ok_iff {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ v, x = .ok v ∧ f v = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem utf8Check_ok {a bad : UInt64} {is : List Instr} (hg : utf8Check a bad = .ok is) :
    ∃ (f4 f7 f9 f11 f13 f17 : Fin 524288) (b20 : Fin 67108864)
      (f22 f24 f28 f32 f34 f36 f38 f40 : Fin 524288) (b43 : Fin 67108864)
      (f45 f47 f51 f55 f59 f61 f63 f65 f67 : Fin 524288) (b70 b73 : Fin 67108864),
      cbField (after a 4) (after a 74) = .ok f4 ∧ cbField (after a 7) (after a 71) = .ok f7 ∧
      cbField (after a 9) bad = .ok f9 ∧ cbField (after a 11) (after a 21) = .ok f11 ∧
      cbField (after a 13) bad = .ok f13 ∧ cbField (after a 17) bad = .ok f17 ∧
      bField (after a 20) (after a 4) = .ok b20 ∧ cbField (after a 22) (after a 44) = .ok f22 ∧
      cbField (after a 24) bad = .ok f24 ∧ cbField (after a 28) bad = .ok f28 ∧
      cbField (after a 32) bad = .ok f32 ∧ cbField (after a 34) (after a 37) = .ok f34 ∧
      cbField (after a 36) bad = .ok f36 ∧ cbField (after a 38) (after a 41) = .ok f38 ∧
      cbField (after a 40) bad = .ok f40 ∧ bField (after a 43) (after a 4) = .ok b43 ∧
      cbField (after a 45) bad = .ok f45 ∧ cbField (after a 47) bad = .ok f47 ∧
      cbField (after a 51) bad = .ok f51 ∧ cbField (after a 55) bad = .ok f55 ∧
      cbField (after a 59) bad = .ok f59 ∧ cbField (after a 61) (after a 64) = .ok f61 ∧
      cbField (after a 63) bad = .ok f63 ∧ cbField (after a 65) (after a 68) = .ok f65 ∧
      cbField (after a 67) bad = .ok f67 ∧ bField (after a 70) (after a 4) = .ok b70 ∧
      bField (after a 73) (after a 4) = .ok b73 ∧
      is = [.addReg 9 17 2, .addImm 9 9 4095, .addImm 9 9 1, .orrReg 10 31 3, .cbz 10 f4,
        .ldrb 11 9 0, .subsImm 31 11 0x80, .bcond 3 f7, .subsImm 31 11 0xC2, .bcond 3 f9,
        .subsImm 31 11 0xE0, .bcond 2 f11,
        .subsImm 31 10 2, .bcond 3 f13,
        .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f17,
        .addImm 9 9 2, .subImm 10 10 2, .b b20,
        .subsImm 31 11 0xF0, .bcond 2 f22,
        .subsImm 31 10 3, .bcond 3 f24,
        .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f28,
        .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f32,
        .subsImm 31 11 0xE0, .bcond 1 f34, .subsImm 31 12 0xA0, .bcond 3 f36,
        .subsImm 31 11 0xED, .bcond 1 f38, .subsImm 31 12 0xA0, .bcond 2 f40,
        .addImm 9 9 3, .subImm 10 10 3, .b b43,
        .subsImm 31 11 0xF5, .bcond 2 f45,
        .subsImm 31 10 4, .bcond 3 f47,
        .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f51,
        .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f55,
        .ldrb 13 9 3, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f59,
        .subsImm 31 11 0xF0, .bcond 1 f61, .subsImm 31 12 0x90, .bcond 3 f63,
        .subsImm 31 11 0xF4, .bcond 1 f65, .subsImm 31 12 0x90, .bcond 2 f67,
        .addImm 9 9 4, .subImm 10 10 4, .b b70,
        .addImm 9 9 1, .subImm 10 10 1, .b b73] := by
  unfold utf8Check at hg
  simp only [bind_eq_ok_iff, pure, Except.pure, Except.ok.injEq] at hg
  obtain ⟨f4, h4, f7, h7, f9, h9, f11, h11, f13, h13, f17, h17, b20, h20, f22, h22, f24, h24,
    f28, h28, f32, h32, f34, h34, f36, h36, f38, h38, f40, h40, b43, h43, f45, h45, f47, h47,
    f51, h51, f55, h55, f59, h59, f61, h61, f63, h63, f65, h65, f67, h67, b70, h70, b73, h73,
    hg⟩ := hg
  exact ⟨f4, f7, f9, f11, f13, f17, b20, f22, f24, f28, f32, f34, f36, f38, f40, b43, f45, f47,
    f51, f55, f59, f61, f63, f65, f67, b70, b73, h4, h7, h9, h11, h13, h17, h20, h22, h24, h28,
    h32, h34, h36, h38, h40, h43, h45, h47, h51, h55, h59, h61, h63, h65, h67, h70, h73,
    hg.symm⟩

/-! ## The bytes and their decision -/

theorem readList_one (m : UInt64 → UInt8) (p : UInt64) (n : Nat) :
    readList m p (n + 1) = m p :: readList m (p + UInt64.ofNat 1) n := rfl

theorem readList_ofNat_succ (m : UInt64 → UInt8) (p : UInt64) (j n : Nat) :
    readList m (p + UInt64.ofNat j) (n + 1) =
      m (p + UInt64.ofNat j) :: readList m (p + UInt64.ofNat (j + 1)) n := by
  rw [readList, show p + UInt64.ofNat j + 1 = p + UInt64.ofNat (j + 1) from add_ofNat_add p j 1]

theorem readList_two (m : UInt64 → UInt8) (p : UInt64) (n : Nat) :
    readList m p (n + 2) =
      m p :: m (p + UInt64.ofNat 1) :: readList m (p + UInt64.ofNat 2) n := by
  have h := readList_ofNat_succ m p 0 (n + 1)
  rw [add_ofNat_zero, readList_ofNat_succ] at h
  exact h

theorem readList_three (m : UInt64 → UInt8) (p : UInt64) (n : Nat) :
    readList m p (n + 3) = m p :: m (p + UInt64.ofNat 1) :: m (p + UInt64.ofNat 2) ::
      readList m (p + UInt64.ofNat 3) n := by
  have h := readList_ofNat_succ m p 0 (n + 2)
  rw [add_ofNat_zero, readList_ofNat_succ, readList_ofNat_succ] at h
  exact h

theorem readList_four (m : UInt64 → UInt8) (p : UInt64) (n : Nat) :
    readList m p (n + 4) = m p :: m (p + UInt64.ofNat 1) :: m (p + UInt64.ofNat 2) ::
      m (p + UInt64.ofNat 3) :: readList m (p + UInt64.ofNat 4) n := by
  have h := readList_ofNat_succ m p 0 (n + 3)
  rw [add_ofNat_zero, readList_ofNat_succ, readList_ofNat_succ, readList_ofNat_succ] at h
  exact h

theorem u8_lt {w c : UInt8} (h : w.toNat < c.toNat) : w < c := UInt8.lt_iff_toNat_lt.mpr h

theorem u8_not_lt {w c : UInt8} (h : c.toNat ≤ w.toNat) : ¬ w < c :=
  fun h' => Nat.not_lt.mpr h (UInt8.lt_iff_toNat_lt.mp h')

theorem contByte_iff (b : UInt8) : contByte b = true ↔ 128 ≤ b.toNat ∧ b.toNat < 192 := by
  simp only [contByte, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
    UInt8.lt_iff_toNat_lt, UInt8.reduceToNat, iff_self]

theorem bne_or_le (w x v c : UInt8) :
    (w != v || decide (c ≤ x)) = decide (¬(w.toNat = v.toNat ∧ x.toNat < c.toNat)) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, decide_eq_true_eq, ne_eq,
    ← UInt8.toNat_inj, UInt8.le_iff_toNat_le]
  omega

theorem bne_or_lt (w x v c : UInt8) :
    (w != v || decide (x < c)) = decide (¬(w.toNat = v.toNat ∧ c.toNat ≤ x.toNat)) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq, decide_eq_true_eq, ne_eq,
    ← UInt8.toNat_inj, UInt8.lt_iff_toNat_lt]
  omega

theorem utf8Scan_one {w : UInt8} (rest : List UInt8) (h : w.toNat < 0x80) :
    utf8Scan (w :: rest) = utf8Scan rest := by
  rw [utf8Scan, if_pos (u8_lt (c := 0x80) h)]

theorem utf8Scan_low {w : UInt8} (rest : List UInt8) (h1 : 0x80 ≤ w.toNat)
    (h2 : w.toNat < 0xC2) : utf8Scan (w :: rest) = false := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) h1), if_pos (u8_lt (c := 0xC2) h2)]

theorem utf8Scan_high {w : UInt8} (rest : List UInt8) (h : 0xF5 ≤ w.toNat) :
    utf8Scan (w :: rest) = false := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) (by show 128 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xC2) (by show 194 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xE0) (by show 224 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xF0) (by show 240 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xF5) h)]

theorem utf8Scan_two {w x : UInt8} (rest : List UInt8) (h1 : 0xC2 ≤ w.toNat)
    (h2 : w.toNat < 0xE0) : utf8Scan (w :: x :: rest) = (contByte x && utf8Scan rest) := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) (by show 128 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xC2) h1), if_pos (u8_lt (c := 0xE0) h2)] <;> rfl

theorem utf8Scan_three {w x y : UInt8} (rest : List UInt8) (h1 : 0xE0 ≤ w.toNat)
    (h2 : w.toNat < 0xF0) :
    utf8Scan (w :: x :: y :: rest) = (contByte x && contByte y &&
      decide (¬(w.toNat = 0xE0 ∧ x.toNat < 0xA0)) &&
      decide (¬(w.toNat = 0xED ∧ 0xA0 ≤ x.toNat)) && utf8Scan rest) := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) (by show 128 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xC2) (by show 194 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xE0) h1), if_pos (u8_lt (c := 0xF0) h2)]
  dsimp only
  rw [bne_or_le, bne_or_lt] <;> rfl

theorem utf8Scan_four {w x y z : UInt8} (rest : List UInt8) (h1 : 0xF0 ≤ w.toNat)
    (h2 : w.toNat < 0xF5) :
    utf8Scan (w :: x :: y :: z :: rest) = (contByte x && contByte y && contByte z &&
      decide (¬(w.toNat = 0xF0 ∧ x.toNat < 0x90)) &&
      decide (¬(w.toNat = 0xF4 ∧ 0x90 ≤ x.toNat)) && utf8Scan rest) := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) (by show 128 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xC2) (by show 194 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xE0) (by show 224 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xF0) h1), if_pos (u8_lt (c := 0xF5) h2)]
  dsimp only
  rw [bne_or_le, bne_or_lt] <;> rfl

/-- A first byte from `0x80` without a byte after it. -/
theorem utf8Scan_short2 {w : UInt8} {rest : List UInt8} (h : 0x80 ≤ w.toNat)
    (hl : rest.length < 1) : utf8Scan (w :: rest) = false := by
  rcases rest with _ | ⟨x, t⟩
  · rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) h)]
    repeat' (first | rfl | split)
  · simp only [List.length_cons] at hl
    omega

/-- A first byte from `0xE0` with fewer than two bytes after it. -/
theorem utf8Scan_short3 {w : UInt8} {rest : List UInt8} (h : 0xE0 ≤ w.toNat)
    (hl : rest.length < 2) : utf8Scan (w :: rest) = false := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) (by show 128 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xC2) (by show 194 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xE0) h)]
  rcases rest with _ | ⟨x, _ | ⟨y, t⟩⟩
  · repeat' (first | rfl | split)
  · repeat' (first | rfl | split)
  · simp only [List.length_cons] at hl
    omega

/-- A first byte from `0xF0` with fewer than three bytes after it. -/
theorem utf8Scan_short4 {w : UInt8} {rest : List UInt8} (h : 0xF0 ≤ w.toNat)
    (hl : rest.length < 3) : utf8Scan (w :: rest) = false := by
  rw [utf8Scan, if_neg (u8_not_lt (c := 0x80) (by show 128 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xC2) (by show 194 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xE0) (by show 224 ≤ w.toNat; omega)),
    if_neg (u8_not_lt (c := 0xF0) h)]
  rcases rest with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · repeat' (first | rfl | split)
  · repeat' (first | rfl | split)
  · repeat' (first | rfl | split)
  · simp only [List.length_cons] at hl
    omega

/-! ## Comparisons of bytes and counts -/

theorem imm_lt {imm : Fin 4096} {k : Nat} (h : imm.val = k) : k < 2 ^ 64 := by
  subst h
  exact Nat.lt_of_lt_of_le imm.isLt (by decide)

theorem byte_lt_ofNat (b : UInt8) {n : Nat} (hn : n < 2 ^ 64) :
    b.toUInt64 < UInt64.ofNat n ↔ b.toNat < n := by
  rw [UInt64.lt_iff_toNat_lt, UInt8.toNat_toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem ofNat_le_byte (b : UInt8) {n : Nat} (hn : n < 2 ^ 64) :
    UInt64.ofNat n ≤ b.toUInt64 ↔ n ≤ b.toNat := by
  rw [UInt64.le_iff_toNat_le, UInt8.toNat_toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

theorem byte_eq_ofNat (b : UInt8) {n : Nat} (hn : n < 2 ^ 64) :
    b.toUInt64 = UInt64.ofNat n ↔ b.toNat = n := by
  rw [← UInt64.toNat_inj, UInt8.toNat_toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn]

/-- The test of a continuation byte: `b - 0x80` lies at or above `0x40` exactly when `b` lies
outside `0x80` to `0xBF`. -/
theorem cont_test (b : UInt8) :
    UInt64.ofNat (0x40 : Fin 4096).val ≤ b.toUInt64 - UInt64.ofNat (0x80 : Fin 4096).val ↔
      ¬ contByte b = true := by
  have hb := byte_lt b
  have e1 : (0x40 : Fin 4096).val = 64 := rfl
  have e2 : (0x80 : Fin 4096).val = 128 := rfl
  rw [contByte_iff, e1, e2, UInt64.le_iff_toNat_le, UInt64.toNat_sub, UInt8.toNat_toUInt64,
    UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  omega

/-! ## The frame and the outcome of a pass -/

/-- The state `t` keeps the registers of `s` other than X9 to X13, SP, the memory, and the UART's
state. -/
structure ScanFrame (s t : State) : Prop where
  regs : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → t.x q = s.x q
  sp : t.sp = s.sp
  mem : t.mem = s.mem
  io : t.io = s.io

theorem ScanFrame.trans {s t u : State} (h1 : ScanFrame s t) (h2 : ScanFrame t u) :
    ScanFrame s u :=
  ⟨fun q a b c d e => (h2.regs q a b c d e).trans (h1.regs q a b c d e), h2.sp.trans h1.sp,
    h2.mem.trans h1.mem, h2.io.trans h1.io⟩

theorem ScanFrame.of_keep {s t : State} (hx : ∀ q : Fin 32, t.x q = s.x q) (hsp : t.sp = s.sp)
    (hm : t.mem = s.mem) (hio : t.io = s.io) : ScanFrame s t :=
  ⟨fun q _ _ _ _ _ => hx q, hsp, hm, hio⟩

theorem fin_ne_of_range {q d : Fin 32} (h9 : q ≠ 9) (h10 : q ≠ 10) (h11 : q ≠ 11)
    (h12 : q ≠ 12) (h13 : q ≠ 13) (hd : 9 ≤ d.val ∧ d.val ≤ 13) : q ≠ d := by
  have a9 : q.val ≠ 9 := fun h => h9 (Fin.ext h)
  have a10 : q.val ≠ 10 := fun h => h10 (Fin.ext h)
  have a11 : q.val ≠ 11 := fun h => h11 (Fin.ext h)
  have a12 : q.val ≠ 12 := fun h => h12 (Fin.ext h)
  have a13 : q.val ≠ 13 := fun h => h13 (Fin.ext h)
  intro h
  have := congrArg Fin.val h
  omega

/-- A run that changes at most the registers `d` and `e` among X9 to X13. -/
theorem ScanFrame.of_regs {s t : State} {d e : Fin 32} (hd : 9 ≤ d.val ∧ d.val ≤ 13)
    (he : 9 ≤ e.val ∧ e.val ≤ 13) (hx : ∀ q : Fin 32, q ≠ d → q ≠ e → t.x q = s.x q)
    (hsp : t.sp = s.sp) (hm : t.mem = s.mem) (hio : t.io = s.io) : ScanFrame s t :=
  ⟨fun q h9 h10 h11 h12 h13 => hx q (fin_ne_of_range h9 h10 h11 h12 h13 hd)
    (fin_ne_of_range h9 h10 h11 h12 h13 he), hsp, hm, hio⟩

/-- The outcome `t` of a pass of the loop of `utf8Check` at `a` over the `r` bytes of `m` from
`p`: the end of the loop, at `after a 74` when `utf8Scan` accepts the bytes and at `bad`
otherwise, or the loop's head with X9 and X10 past the `c` bytes of a character that `utf8Scan`
accepts. -/
def Utf8Pass (a bad p : UInt64) (m : UInt64 → UInt8) (r : Nat) (t : State) : Prop :=
  (t.pc = if utf8Scan (readList m p r) then after a 74 else bad) ∨
    ∃ c r', r = r' + c ∧ 0 < c ∧ t.pc = after a 4 ∧ t.x 9 = p + UInt64.ofNat c ∧
      t.x 10 = UInt64.ofNat r' ∧
      utf8Scan (readList m p r) = utf8Scan (readList m (p + UInt64.ofNat c) r')

theorem pc_bad {L : List UInt8} {ok bad pc : UInt64} (hL : utf8Scan L = false) (h : pc = bad) :
    pc = if utf8Scan L then ok else bad := by
  simp [hL, h]

theorem pc_ok {L : List UInt8} {ok bad pc : UInt64} (hL : utf8Scan L = true) (h : pc = ok) :
    pc = if utf8Scan L then ok else bad := by
  simp [hL, h]

/-! ## Steps and comparisons -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- A step of `LDRB Wt, [Xn, #imm]` of Normal memory, with a base other than SP. -/
theorem step_ldrb {s : State} {t n : Fin 32} {imm : Fin 4096} (ht : t.val < 31)
    (hn : n.val < 31) (hc : code s.pc = some (encode (.ldrb t n imm)))
    (hmap : P.normal (s.x n + UInt64.ofNat imm.val) = true) :
    ∃ u, Reach P code s u ∧ u.pc = s.pc + 4 ∧
      u.x t = (s.mem (s.x n + UInt64.ofNat imm.val)).toUInt64 ∧
      (∀ q : Fin 32, q ≠ t → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem ∧ u.io = s.io :=
  step_setX P code ht hc (exec_ldrb_base P hn hmap)

/-- A step of `SUB Xd, Xn, #imm` with registers other than SP. -/
theorem step_subImm {s : State} {d n : Fin 32} {imm : Fin 4096} (hd : d.val < 31)
    (hn : n.val < 31) (hc : code s.pc = some (encode (.subImm d n imm))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = s.x n - UInt64.ofNat imm.val ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  step_setX P code hd hc (exec_subImm_x P hd hn)

/-- `SUBS XZR, Xr, #imm` and `B.HS` to `tB`: the branch is taken when X`r` lies at or above
`imm`. -/
theorem run_hsImm {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288}
    (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 2 g])
    (hg : after a 1 + sext 19 g.val * 4 = tB) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ (t.pc = if UInt64.ofNat imm.val ≤ s.x r then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  let s1 : State := { s.subs 31 (s.x r) (UInt64.ofNat imm.val) with pc := s.pc + 4 }
  have e1 : LeanExe.A64.exec P (.subsImm 31 r imm) s = some s1 := by
    simp only [exec, State.xsp_eq_x hr]
    rfl
  let s2 : State :=
    { s1 with pc := if s1.condHolds 2 then s1.pc + sext 19 g.val * 4 else s1.pc + 4 }
  have e2 : LeanExe.A64.exec P (.bcond 2 g) s1 = some s2 := rfl
  have p1 : s1.pc = after a 1 := by show s.pc + 4 = _; rw [hpc, after_one]
  have hx1 : ∀ q : Fin 32, s1.x q = s.x q := fun q => by
    show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have hcond : s1.condHolds 2 = decide (UInt64.ofNat imm.val ≤ s.x r) := rfl
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c0) e1
      (reach_exec P code (by rw [p1]; exact c1) e2 (.refl _)), ?_, hx1, ?_, ?_, ?_⟩
  · show (if s1.condHolds 2 then s1.pc + sext 19 g.val * 4 else s1.pc + 4) = _
    rw [hcond, p1]
    by_cases h : UInt64.ofNat imm.val ≤ s.x r
    · rw [ite_eq_left (by simpa using h), ite_eq_left h]
      exact hg
    · rw [ite_eq_right (by simpa using h), ite_eq_right h, ← after_succ]
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).sp = _
    exact State.setX_sp
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).mem = _
    exact State.setX_mem
  · show (s.setX 31 (s.x r - UInt64.ofNat imm.val)).io = _
    exact State.setX_io

/-- `SUBS XZR, Xr, #imm` and `B.LO` to `tB` on a register that holds the byte `b`. -/
theorem run_byteLo {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288} {k : Nat}
    {b : UInt8} (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 3 g])
    (hk : imm.val = k) (hg : cbField (after a 1) tB = .ok g) {s : State} (hpc : s.pc = a)
    (hb : s.x r = b.toUInt64) :
    ∃ t, Reach P code s t ∧ (t.pc = if b.toNat < k then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨t, h1, h2, h3⟩ := run_loImm P code hr hcode (cbField_target hg) hpc
  refine ⟨t, h1, ?_, h3⟩
  rw [h2, hb, hk]
  by_cases h : b.toNat < k
  · rw [if_pos ((byte_lt_ofNat b (imm_lt hk)).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((byte_lt_ofNat b (imm_lt hk)).mp h')), if_neg h]

/-- `SUBS XZR, Xr, #imm` and `B.HS` to `tB` on a register that holds the byte `b`. -/
theorem run_byteHs {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288} {k : Nat}
    {b : UInt8} (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 2 g])
    (hk : imm.val = k) (hg : cbField (after a 1) tB = .ok g) {s : State} (hpc : s.pc = a)
    (hb : s.x r = b.toUInt64) :
    ∃ t, Reach P code s t ∧ (t.pc = if k ≤ b.toNat then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨t, h1, h2, h3⟩ := run_hsImm P code hr hcode (cbField_target hg) hpc
  refine ⟨t, h1, ?_, h3⟩
  rw [h2, hb, hk]
  by_cases h : k ≤ b.toNat
  · rw [if_pos ((ofNat_le_byte b (imm_lt hk)).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((ofNat_le_byte b (imm_lt hk)).mp h')), if_neg h]

/-- `SUBS XZR, Xr, #imm` and `B.LO` to `tB` on a register that holds the count `c`. -/
theorem run_countLo {a tB : UInt64} {r : Fin 32} {imm : Fin 4096} {g : Fin 524288} {k c : Nat}
    (hr : r.val < 31) (hcode : CodeAt code a [.subsImm 31 r imm, .bcond 3 g])
    (hk : imm.val = k) (hg : cbField (after a 1) tB = .ok g) {s : State} (hpc : s.pc = a)
    (hc : s.x r = UInt64.ofNat c) (hc64 : c < 2 ^ 64) :
    ∃ t, Reach P code s t ∧ (t.pc = if c < k then tB else after a 2) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨t, h1, h2, h3⟩ := run_loImm P code hr hcode (cbField_target hg) hpc
  refine ⟨t, h1, ?_, h3⟩
  rw [h2, hc, hk]
  by_cases h : c < k
  · rw [if_pos ((ofNat_lt_ofNat hc64 (imm_lt hk)).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((ofNat_lt_ofNat hc64 (imm_lt hk)).mp h')), if_neg h]

/-- The test of a second byte `x` in X12 after the first byte `w` in X11: `SUBS XZR, X11, #v`,
`B.NE` past the next test, `SUBS XZR, X12, #c`, and `B.LO` to `tB`. -/
theorem run_neLo {a tB : UInt64} {imm1 imm2 : Fin 4096} {g1 g3 : Fin 524288} {n1 n2 : Nat}
    {w x : UInt8}
    (hcode : CodeAt code a [.subsImm 31 11 imm1, .bcond 1 g1, .subsImm 31 12 imm2, .bcond 3 g3])
    (hn1 : imm1.val = n1) (hn2 : imm2.val = n2)
    (hg1 : cbField (after a 1) (after a 4) = .ok g1) (hg3 : cbField (after a 3) tB = .ok g3)
    {s : State} (hpc : s.pc = a) (hw : s.x 11 = w.toUInt64) (hx : s.x 12 = x.toUInt64) :
    ∃ t, Reach P code s t ∧ (t.pc = if w.toNat = n1 ∧ x.toNat < n2 then tB else after a 4) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have hc := CodeAt.split code (n := 2) (l1 := [.subsImm 31 11 imm1, .bcond 1 g1]) hcode rfl
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_neImm P code (by decide) hc.1
    (cbField_target hg1) hpc
  rw [hw, hn1] at p1
  by_cases he : w.toNat = n1
  · rw [if_pos ((byte_eq_ofNat w (imm_lt hn1)).mpr he)] at p1
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_byteLo P code (r := 12) (imm := imm2) (b := x)
      (by decide) hc.2 hn2 (by rw [after_after]; exact hg3) p1 (by rw [k1, hx])
    refine ⟨u2, r1.trans r2, ?_, fun q => (k2 q).trans (k1 q), sp2.trans sp1, m2.trans m1,
      io2.trans io1⟩
    rw [p2, after_after]
    by_cases hl : x.toNat < n2
    · rw [if_pos hl, if_pos ⟨he, hl⟩]
    · rw [if_neg hl, if_neg (fun h => hl h.2)]
  · rw [if_neg (fun h => he ((byte_eq_ofNat w (imm_lt hn1)).mp h))] at p1
    exact ⟨u1, r1, by rw [p1, if_neg (fun h => he h.1)], k1, sp1, m1, io1⟩

/-- The test of a second byte `x` in X12 after the first byte `w` in X11: `SUBS XZR, X11, #v`,
`B.NE` past the next test, `SUBS XZR, X12, #c`, and `B.HS` to `tB`. -/
theorem run_neHs {a tB : UInt64} {imm1 imm2 : Fin 4096} {g1 g3 : Fin 524288} {n1 n2 : Nat}
    {w x : UInt8}
    (hcode : CodeAt code a [.subsImm 31 11 imm1, .bcond 1 g1, .subsImm 31 12 imm2, .bcond 2 g3])
    (hn1 : imm1.val = n1) (hn2 : imm2.val = n2)
    (hg1 : cbField (after a 1) (after a 4) = .ok g1) (hg3 : cbField (after a 3) tB = .ok g3)
    {s : State} (hpc : s.pc = a) (hw : s.x 11 = w.toUInt64) (hx : s.x 12 = x.toUInt64) :
    ∃ t, Reach P code s t ∧ (t.pc = if w.toNat = n1 ∧ n2 ≤ x.toNat then tB else after a 4) ∧
      (∀ q : Fin 32, t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  have hc := CodeAt.split code (n := 2) (l1 := [.subsImm 31 11 imm1, .bcond 1 g1]) hcode rfl
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_neImm P code (by decide) hc.1
    (cbField_target hg1) hpc
  rw [hw, hn1] at p1
  by_cases he : w.toNat = n1
  · rw [if_pos ((byte_eq_ofNat w (imm_lt hn1)).mpr he)] at p1
    obtain ⟨u2, r2, p2, k2, sp2, m2, io2⟩ := run_byteHs P code (r := 12) (imm := imm2) (b := x)
      (by decide) hc.2 hn2 (by rw [after_after]; exact hg3) p1 (by rw [k1, hx])
    refine ⟨u2, r1.trans r2, ?_, fun q => (k2 q).trans (k1 q), sp2.trans sp1, m2.trans m1,
      io2.trans io1⟩
    rw [p2, after_after]
    by_cases hl : n2 ≤ x.toNat
    · rw [if_pos hl, if_pos ⟨he, hl⟩]
    · rw [if_neg hl, if_neg (fun h => hl h.2)]
  · rw [if_neg (fun h => he ((byte_eq_ofNat w (imm_lt hn1)).mp h))] at p1
    exact ⟨u1, r1, by rw [p1, if_neg (fun h => he h.1)], k1, sp1, m1, io1⟩

/-- `LDRB Wd, [X9, #j]` and the test that the byte is a continuation byte, with `B.HS` to `tB`
otherwise, through X13. -/
theorem run_cont {a tB : UInt64} {d : Fin 32} {k : Fin 4096} {j : Nat} {g : Fin 524288}
    (hd : d.val < 31)
    (hcode : CodeAt code a [.ldrb d 9 k, .subImm 13 d 0x80, .subsImm 31 13 0x40, .bcond 2 g])
    (hk : k.val = j) (hg : cbField (after a 3) tB = .ok g) {s : State} (hpc : s.pc = a)
    (hmap : P.normal (s.x 9 + UInt64.ofNat j) = true) :
    ∃ t, Reach P code s t ∧
      (t.pc = if contByte (s.mem (s.x 9 + UInt64.ofNat j)) then after a 4 else tB) ∧
      (d ≠ 13 → t.x d = (s.mem (s.x 9 + UInt64.ofNat j)).toUInt64) ∧
      (∀ q : Fin 32, q ≠ d → q ≠ 13 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  subst hk
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
  have c23 : CodeAt code (after a 2) [.subsImm 31 13 0x40, .bcond 2 g] := by
    simpa using CodeAt.drop_take code hcode 2 2 (by simp)
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_ldrb P code (s := s) (t := d) (n := 9)
    (imm := k) hd (by decide) (by rw [hpc]; exact c0) hmap
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_subImm P code (s := u1) (d := 13) (n := d)
    (imm := 0x80) (by decide) hd (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_hsImm P code (r := 13) (imm := 0x40) (tB := tB)
    (by decide) c23 (by rw [after_after]; exact cbField_target hg) q2
  refine ⟨u3, r1.trans (r2.trans r3), ?_, fun h => by rw [k3, k2 d h, x1],
    fun q hq h13 => by rw [k3, k2 q h13, k1 q hq], by rw [sp3, sp2, sp1], by rw [m3, m2, m1],
    by rw [io3, io2, io1]⟩
  rw [p3, x2, x1, after_after]
  by_cases hb : contByte (s.mem (s.x 9 + UInt64.ofNat k.val)) = true
  · rw [if_neg (fun h => (cont_test _).mp h hb), if_pos hb]
  · rw [if_pos ((cont_test _).mpr hb), if_neg hb]

/-- `ADD X9, X9, #c`, `SUB X10, X10, #c`, and `B` to `tB`. -/
theorem run_next {a tB : UInt64} {c : Fin 4096} {k : Nat} {g : Fin 67108864}
    (hcode : CodeAt code a [.addImm 9 9 c, .subImm 10 10 c, .b g]) (hk : c.val = k)
    (hg : bField (after a 2) tB = .ok g) {s : State} (hpc : s.pc = a) :
    ∃ t, Reach P code s t ∧ t.pc = tB ∧ t.x 9 = s.x 9 + UInt64.ofNat k ∧
      t.x 10 = s.x 10 - UInt64.ofNat k ∧ (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  subst hk
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addImm P code (s := s) (d := 9) (n := 9)
    (imm := c) (by decide) (by decide) (by rw [hpc]; exact c0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_subImm P code (s := u1) (d := 10) (n := 10)
    (imm := c) (by decide) (by decide) (by rw [q1]; exact c1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := step_b P code (s := u2) (target := tB)
    (by rw [q2]; exact c2) (by rw [q2]; exact bField_target hg)
  exact ⟨u3, r1.trans (r2.trans r3), p3, by rw [k3, k2 9 (by decide), x1],
    by rw [k3, x2, k1 10 (by decide)], fun q h9 h10 => by rw [k3, k2 q h10, k1 q h9],
    by rw [sp3, sp2, sp1], by rw [m3, m2, m1], by rw [io3, io2, io1]⟩

/-! ## The characters' runs -/

/-- The run of a two-byte character from `after a 12`, with its first byte `w` at `p` in X9 and
the `r` bytes that remain in X10. -/
theorem run_utf8Two {a bad : UInt64} {f13 f17 : Fin 524288} {b20 : Fin 67108864}
    (hcode : CodeAt code (after a 12) [.subsImm 31 10 2, .bcond 3 f13,
      .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f17,
      .addImm 9 9 2, .subImm 10 10 2, .b b20])
    (h13 : cbField (after a 13) bad = .ok f13) (h17 : cbField (after a 17) bad = .ok f17)
    (h20 : bField (after a 20) (after a 4) = .ok b20)
    {r : Nat} {w : UInt8} {p : UInt64} {s : State} (hpc : s.pc = after a 12)
    (h9 : s.x 9 = p) (h10 : s.x 10 = UInt64.ofNat r) (hr64 : r < 2 ^ 64)
    (hmap : ∀ k < r, P.normal (p + UInt64.ofNat k) = true)
    (hw : s.mem p = w) (hr0 : 0 < r) (c1 : 0xC2 ≤ w.toNat) (c2 : w.toNat < 0xE0) :
    ∃ t, Reach P code s t ∧ ScanFrame s t ∧ Utf8Pass a bad p s.mem r t := by
  have c0 : CodeAt code (after a 12) [.subsImm 31 10 2, .bcond 3 f13] := by
    simpa [after_after] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c2' : CodeAt code (after a 14)
      [.ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f17] := by
    simpa [after_after] using CodeAt.drop_take code hcode 2 4 (by simp)
  have c6 : CodeAt code (after a 18) [.addImm 9 9 2, .subImm 10 10 2, .b b20] := by
    simpa [after_after] using CodeAt.drop_take code hcode 6 3 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_countLo P code (r := 10) (imm := 2) (k := 2)
    (tB := bad) (by decide) c0 rfl (by rw [after_after]; exact h13) hpc h10 hr64
  have F1 := ScanFrame.of_keep k1 sp1 m1 io1
  by_cases c4 : r < 2
  · rw [if_pos c4] at p1
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    refine ⟨u1, r1, F1, Or.inl (pc_bad ?_ p1)⟩
    rw [readList_one, hw]
    exact utf8Scan_short2 (by omega) (by rw [readList_length]; omega)
  rw [if_neg c4, after_after] at p1
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  obtain ⟨u2, r2, p2, -, k2, sp2, m2, io2⟩ := run_cont P code (d := 12) (k := 1) (j := 1)
    (tB := bad) (by decide) c2' rfl (by rw [after_after]; exact h17) p1
    (by rw [k1, h9]; exact hmap 1 (by omega))
  rw [k1, h9, m1] at p2
  have F2 := F1.trans (ScanFrame.of_regs (d := 12) (e := 13) (by decide) (by decide) k2 sp2 m2
    io2)
  by_cases cx : contByte (s.mem (p + UInt64.ofNat 1)) = true
  · rw [if_pos cx, after_after] at p2
    obtain ⟨u3, r3, p3, x93, x103, k3, sp3, m3, io3⟩ := run_next P code (c := 2) (k := 2)
      (tB := after a 4) c6 rfl (by rw [after_after]; exact h20) p2
    refine ⟨u3, r1.trans (r2.trans r3), F2.trans (ScanFrame.of_regs (d := 9) (e := 10)
      (by decide) (by decide) k3 sp3 m3 io3), Or.inr ⟨2, n, rfl, by omega, p3, ?_, ?_, ?_⟩⟩
    · rw [x93, k2 9 (by decide) (by decide), k1, h9]
    · rw [x103, k2 10 (by decide) (by decide), k1, h10, ofNat_sub_ofNat (r := 2) (by omega) hr64,
        Nat.add_sub_cancel]
    · rw [readList_two, hw, utf8Scan_two _ c1 c2, cx, Bool.true_and]
  · rw [if_neg cx] at p2
    refine ⟨u2, r1.trans r2, F2, Or.inl (pc_bad ?_ p2)⟩
    rw [readList_two, hw, utf8Scan_two _ c1 c2, Bool.eq_false_iff.mpr cx, Bool.false_and]

/-- The run of a three-byte character from `after a 23`, with its first byte `w` at `p` in X9
and in X11 and the `r` bytes that remain in X10. -/
theorem run_utf8Three {a bad : UInt64} {f24 f28 f32 f34 f36 f38 f40 : Fin 524288}
    {b43 : Fin 67108864}
    (hcode : CodeAt code (after a 23) [.subsImm 31 10 3, .bcond 3 f24,
      .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f28,
      .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f32,
      .subsImm 31 11 0xE0, .bcond 1 f34, .subsImm 31 12 0xA0, .bcond 3 f36,
      .subsImm 31 11 0xED, .bcond 1 f38, .subsImm 31 12 0xA0, .bcond 2 f40,
      .addImm 9 9 3, .subImm 10 10 3, .b b43])
    (h24 : cbField (after a 24) bad = .ok f24) (h28 : cbField (after a 28) bad = .ok f28)
    (h32 : cbField (after a 32) bad = .ok f32) (h34 : cbField (after a 34) (after a 37) = .ok f34)
    (h36 : cbField (after a 36) bad = .ok f36) (h38 : cbField (after a 38) (after a 41) = .ok f38)
    (h40 : cbField (after a 40) bad = .ok f40) (h43 : bField (after a 43) (after a 4) = .ok b43)
    {r : Nat} {w : UInt8} {p : UInt64} {s : State} (hpc : s.pc = after a 23)
    (h9 : s.x 9 = p) (h10 : s.x 10 = UInt64.ofNat r) (h11 : s.x 11 = w.toUInt64)
    (hr64 : r < 2 ^ 64) (hmap : ∀ k < r, P.normal (p + UInt64.ofNat k) = true)
    (hw : s.mem p = w) (hr0 : 0 < r) (c1 : 0xE0 ≤ w.toNat) (c2 : w.toNat < 0xF0) :
    ∃ t, Reach P code s t ∧ ScanFrame s t ∧ Utf8Pass a bad p s.mem r t := by
  have c0 : CodeAt code (after a 23) [.subsImm 31 10 3, .bcond 3 f24] := by
    simpa [after_after] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c2' : CodeAt code (after a 25)
      [.ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f28] := by
    simpa [after_after] using CodeAt.drop_take code hcode 2 4 (by simp)
  have c6 : CodeAt code (after a 29)
      [.ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f32] := by
    simpa [after_after] using CodeAt.drop_take code hcode 6 4 (by simp)
  have c10 : CodeAt code (after a 33)
      [.subsImm 31 11 0xE0, .bcond 1 f34, .subsImm 31 12 0xA0, .bcond 3 f36] := by
    simpa [after_after] using CodeAt.drop_take code hcode 10 4 (by simp)
  have c14 : CodeAt code (after a 37)
      [.subsImm 31 11 0xED, .bcond 1 f38, .subsImm 31 12 0xA0, .bcond 2 f40] := by
    simpa [after_after] using CodeAt.drop_take code hcode 14 4 (by simp)
  have c18 : CodeAt code (after a 41) [.addImm 9 9 3, .subImm 10 10 3, .b b43] := by
    simpa [after_after] using CodeAt.drop_take code hcode 18 3 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_countLo P code (r := 10) (imm := 3) (k := 3)
    (tB := bad) (by decide) c0 rfl (by rw [after_after]; exact h24) hpc h10 hr64
  have F1 := ScanFrame.of_keep k1 sp1 m1 io1
  by_cases c4 : r < 3
  · rw [if_pos c4] at p1
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    refine ⟨u1, r1, F1, Or.inl (pc_bad ?_ p1)⟩
    rw [readList_one, hw]
    exact utf8Scan_short3 c1 (by rw [readList_length]; omega)
  rw [if_neg c4, after_after] at p1
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 3 := ⟨r - 3, by omega⟩
  have hL := readList_three s.mem p n
  rw [hw] at hL
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_cont P code (d := 12) (k := 1) (j := 1)
    (tB := bad) (by decide) c2' rfl (by rw [after_after]; exact h28) p1
    (by rw [k1, h9]; exact hmap 1 (by omega))
  rw [k1, h9, m1] at p2 x2
  obtain ⟨x, hx⟩ : ∃ x, s.mem (p + UInt64.ofNat 1) = x := ⟨_, rfl⟩
  rw [hx] at p2 x2 hL
  have F2 := F1.trans (ScanFrame.of_regs (d := 12) (e := 13) (by decide) (by decide) k2 sp2 m2
    io2)
  by_cases cx : contByte x = true
  swap
  · rw [if_neg cx] at p2
    refine ⟨u2, r1.trans r2, F2, Or.inl (pc_bad ?_ p2)⟩
    simp only [hL, utf8Scan_three _ c1 c2, Bool.eq_false_iff.mpr cx, Bool.false_and]
  rw [if_pos cx, after_after] at p2
  have e9 : u2.x 9 = p := by rw [k2 9 (by decide) (by decide), k1, h9]
  have em : u2.mem = s.mem := by rw [m2, m1]
  obtain ⟨u3, r3, p3, -, k3, sp3, m3, io3⟩ := run_cont P code (d := 13) (k := 2) (j := 2)
    (tB := bad) (by decide) c6 rfl (by rw [after_after]; exact h32) p2
    (by rw [e9]; exact hmap 2 (by omega))
  rw [e9, em] at p3
  obtain ⟨y, hy⟩ : ∃ y, s.mem (p + UInt64.ofNat 2) = y := ⟨_, rfl⟩
  rw [hy] at p3 hL
  have F3 := F2.trans (ScanFrame.of_regs (d := 13) (e := 13) (by decide) (by decide) k3 sp3 m3
    io3)
  by_cases cy : contByte y = true
  swap
  · rw [if_neg cy] at p3
    refine ⟨u3, r1.trans (r2.trans r3), F3, Or.inl (pc_bad ?_ p3)⟩
    simp only [hL, utf8Scan_three _ c1 c2, cx, Bool.eq_false_iff.mpr cy, Bool.true_and,
      Bool.false_and]
  rw [if_pos cy, after_after] at p3
  have hx11 : u3.x 11 = w.toUInt64 := by
    rw [k3 11 (by decide) (by decide), k2 11 (by decide) (by decide), k1, h11]
  have hx12 : u3.x 12 = x.toUInt64 := by rw [k3 12 (by decide) (by decide), x2 (by decide)]
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_neLo P code (imm1 := 0xE0) (imm2 := 0xA0)
    (n1 := 0xE0) (n2 := 0xA0) (tB := bad) c10 rfl rfl
    (by rw [after_after, after_after]; exact h34) (by rw [after_after]; exact h36) p3 hx11 hx12
  have F4 := F3.trans (ScanFrame.of_keep k4 sp4 m4 io4)
  by_cases cE : w.toNat = 0xE0 ∧ x.toNat < 0xA0
  · rw [if_pos cE] at p4
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), F4, Or.inl (pc_bad ?_ p4)⟩
    simp only [hL, utf8Scan_three _ c1 c2, cx, cy, decide_eq_false (not_not_intro cE),
      Bool.true_and, Bool.false_and]
  rw [if_neg cE, after_after] at p4
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_neHs P code (imm1 := 0xED) (imm2 := 0xA0)
    (n1 := 0xED) (n2 := 0xA0) (tB := bad) c14 rfl rfl
    (by rw [after_after, after_after]; exact h38) (by rw [after_after]; exact h40) p4
    (by rw [k4, hx11]) (by rw [k4, hx12])
  have F5 := F4.trans (ScanFrame.of_keep k5 sp5 m5 io5)
  by_cases cD : w.toNat = 0xED ∧ 0xA0 ≤ x.toNat
  · rw [if_pos cD] at p5
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), F5, Or.inl (pc_bad ?_ p5)⟩
    simp only [hL, utf8Scan_three _ c1 c2, cx, cy, decide_eq_true cE,
      decide_eq_false (not_not_intro cD), Bool.true_and, Bool.false_and]
  rw [if_neg cD, after_after] at p5
  obtain ⟨u6, r6, p6, x96, x106, k6, sp6, m6, io6⟩ := run_next P code (c := 3) (k := 3)
    (tB := after a 4) c18 rfl (by rw [after_after]; exact h43) p5
  refine ⟨u6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))),
    F5.trans (ScanFrame.of_regs (d := 9) (e := 10) (by decide) (by decide) k6 sp6 m6 io6),
    Or.inr ⟨3, n, rfl, by omega, p6, ?_, ?_, ?_⟩⟩
  · rw [x96, k5, k4, k3 9 (by decide) (by decide), e9]
  · rw [x106, k5, k4, k3 10 (by decide) (by decide), k2 10 (by decide) (by decide), k1, h10,
      ofNat_sub_ofNat (r := 3) (by omega) hr64, Nat.add_sub_cancel]
  · simp only [hL, utf8Scan_three _ c1 c2, cx, cy, decide_eq_true cE, decide_eq_true cD,
      Bool.true_and]

/-- The run of a four-byte character from `after a 46`, with its first byte `w` at `p` in X9
and in X11 and the `r` bytes that remain in X10. -/
theorem run_utf8Four {a bad : UInt64} {f47 f51 f55 f59 f61 f63 f65 f67 : Fin 524288}
    {b70 : Fin 67108864}
    (hcode : CodeAt code (after a 46) [.subsImm 31 10 4, .bcond 3 f47,
      .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f51,
      .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f55,
      .ldrb 13 9 3, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f59,
      .subsImm 31 11 0xF0, .bcond 1 f61, .subsImm 31 12 0x90, .bcond 3 f63,
      .subsImm 31 11 0xF4, .bcond 1 f65, .subsImm 31 12 0x90, .bcond 2 f67,
      .addImm 9 9 4, .subImm 10 10 4, .b b70])
    (h47 : cbField (after a 47) bad = .ok f47) (h51 : cbField (after a 51) bad = .ok f51)
    (h55 : cbField (after a 55) bad = .ok f55) (h59 : cbField (after a 59) bad = .ok f59)
    (h61 : cbField (after a 61) (after a 64) = .ok f61) (h63 : cbField (after a 63) bad = .ok f63)
    (h65 : cbField (after a 65) (after a 68) = .ok f65) (h67 : cbField (after a 67) bad = .ok f67)
    (h70 : bField (after a 70) (after a 4) = .ok b70)
    {r : Nat} {w : UInt8} {p : UInt64} {s : State} (hpc : s.pc = after a 46)
    (h9 : s.x 9 = p) (h10 : s.x 10 = UInt64.ofNat r) (h11 : s.x 11 = w.toUInt64)
    (hr64 : r < 2 ^ 64) (hmap : ∀ k < r, P.normal (p + UInt64.ofNat k) = true)
    (hw : s.mem p = w) (hr0 : 0 < r) (c1 : 0xF0 ≤ w.toNat) (c2 : w.toNat < 0xF5) :
    ∃ t, Reach P code s t ∧ ScanFrame s t ∧ Utf8Pass a bad p s.mem r t := by
  have c0 : CodeAt code (after a 46) [.subsImm 31 10 4, .bcond 3 f47] := by
    simpa [after_after] using CodeAt.drop_take code hcode 0 2 (by simp)
  have c2' : CodeAt code (after a 48)
      [.ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f51] := by
    simpa [after_after] using CodeAt.drop_take code hcode 2 4 (by simp)
  have c6 : CodeAt code (after a 52)
      [.ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f55] := by
    simpa [after_after] using CodeAt.drop_take code hcode 6 4 (by simp)
  have c10 : CodeAt code (after a 56)
      [.ldrb 13 9 3, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f59] := by
    simpa [after_after] using CodeAt.drop_take code hcode 10 4 (by simp)
  have c14 : CodeAt code (after a 60)
      [.subsImm 31 11 0xF0, .bcond 1 f61, .subsImm 31 12 0x90, .bcond 3 f63] := by
    simpa [after_after] using CodeAt.drop_take code hcode 14 4 (by simp)
  have c18 : CodeAt code (after a 64)
      [.subsImm 31 11 0xF4, .bcond 1 f65, .subsImm 31 12 0x90, .bcond 2 f67] := by
    simpa [after_after] using CodeAt.drop_take code hcode 18 4 (by simp)
  have c22 : CodeAt code (after a 68) [.addImm 9 9 4, .subImm 10 10 4, .b b70] := by
    simpa [after_after] using CodeAt.drop_take code hcode 22 3 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := run_countLo P code (r := 10) (imm := 4) (k := 4)
    (tB := bad) (by decide) c0 rfl (by rw [after_after]; exact h47) hpc h10 hr64
  have F1 := ScanFrame.of_keep k1 sp1 m1 io1
  by_cases c4 : r < 4
  · rw [if_pos c4] at p1
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    refine ⟨u1, r1, F1, Or.inl (pc_bad ?_ p1)⟩
    rw [readList_one, hw]
    exact utf8Scan_short4 c1 (by rw [readList_length]; omega)
  rw [if_neg c4, after_after] at p1
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 4 := ⟨r - 4, by omega⟩
  have hL := readList_four s.mem p n
  rw [hw] at hL
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := run_cont P code (d := 12) (k := 1) (j := 1)
    (tB := bad) (by decide) c2' rfl (by rw [after_after]; exact h51) p1
    (by rw [k1, h9]; exact hmap 1 (by omega))
  rw [k1, h9, m1] at p2 x2
  obtain ⟨x, hx⟩ : ∃ x, s.mem (p + UInt64.ofNat 1) = x := ⟨_, rfl⟩
  rw [hx] at p2 x2 hL
  have F2 := F1.trans (ScanFrame.of_regs (d := 12) (e := 13) (by decide) (by decide) k2 sp2 m2
    io2)
  by_cases cx : contByte x = true
  swap
  · rw [if_neg cx] at p2
    refine ⟨u2, r1.trans r2, F2, Or.inl (pc_bad ?_ p2)⟩
    simp only [hL, utf8Scan_four _ c1 c2, Bool.eq_false_iff.mpr cx, Bool.false_and]
  rw [if_pos cx, after_after] at p2
  have e9 : u2.x 9 = p := by rw [k2 9 (by decide) (by decide), k1, h9]
  have em : u2.mem = s.mem := by rw [m2, m1]
  obtain ⟨u3, r3, p3, -, k3, sp3, m3, io3⟩ := run_cont P code (d := 13) (k := 2) (j := 2)
    (tB := bad) (by decide) c6 rfl (by rw [after_after]; exact h55) p2
    (by rw [e9]; exact hmap 2 (by omega))
  rw [e9, em] at p3
  obtain ⟨y, hy⟩ : ∃ y, s.mem (p + UInt64.ofNat 2) = y := ⟨_, rfl⟩
  rw [hy] at p3 hL
  have F3 := F2.trans (ScanFrame.of_regs (d := 13) (e := 13) (by decide) (by decide) k3 sp3 m3
    io3)
  by_cases cy : contByte y = true
  swap
  · rw [if_neg cy] at p3
    refine ⟨u3, r1.trans (r2.trans r3), F3, Or.inl (pc_bad ?_ p3)⟩
    simp only [hL, utf8Scan_four _ c1 c2, cx, Bool.eq_false_iff.mpr cy, Bool.true_and,
      Bool.false_and]
  rw [if_pos cy, after_after] at p3
  have e9' : u3.x 9 = p := by rw [k3 9 (by decide) (by decide), e9]
  have em' : u3.mem = s.mem := by rw [m3, em]
  obtain ⟨u4, r4, p4, -, k4, sp4, m4, io4⟩ := run_cont P code (d := 13) (k := 3) (j := 3)
    (tB := bad) (by decide) c10 rfl (by rw [after_after]; exact h59) p3
    (by rw [e9']; exact hmap 3 (by omega))
  rw [e9', em'] at p4
  obtain ⟨z, hz⟩ : ∃ z, s.mem (p + UInt64.ofNat 3) = z := ⟨_, rfl⟩
  rw [hz] at p4 hL
  have F4 := F3.trans (ScanFrame.of_regs (d := 13) (e := 13) (by decide) (by decide) k4 sp4 m4
    io4)
  by_cases cz : contByte z = true
  swap
  · rw [if_neg cz] at p4
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), F4, Or.inl (pc_bad ?_ p4)⟩
    simp only [hL, utf8Scan_four _ c1 c2, cx, cy, Bool.eq_false_iff.mpr cz, Bool.true_and,
      Bool.false_and]
  rw [if_pos cz, after_after] at p4
  have hx11 : u4.x 11 = w.toUInt64 := by
    rw [k4 11 (by decide) (by decide), k3 11 (by decide) (by decide),
      k2 11 (by decide) (by decide), k1, h11]
  have hx12 : u4.x 12 = x.toUInt64 := by
    rw [k4 12 (by decide) (by decide), k3 12 (by decide) (by decide), x2 (by decide)]
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_neLo P code (imm1 := 0xF0) (imm2 := 0x90)
    (n1 := 0xF0) (n2 := 0x90) (tB := bad) c14 rfl rfl
    (by rw [after_after, after_after]; exact h61) (by rw [after_after]; exact h63) p4 hx11 hx12
  have F5 := F4.trans (ScanFrame.of_keep k5 sp5 m5 io5)
  by_cases cF : w.toNat = 0xF0 ∧ x.toNat < 0x90
  · rw [if_pos cF] at p5
    refine ⟨u5, r1.trans (r2.trans (r3.trans (r4.trans r5))), F5, Or.inl (pc_bad ?_ p5)⟩
    simp only [hL, utf8Scan_four _ c1 c2, cx, cy, cz, decide_eq_false (not_not_intro cF),
      Bool.true_and, Bool.false_and]
  rw [if_neg cF, after_after] at p5
  obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := run_neHs P code (imm1 := 0xF4) (imm2 := 0x90)
    (n1 := 0xF4) (n2 := 0x90) (tB := bad) c18 rfl rfl
    (by rw [after_after, after_after]; exact h65) (by rw [after_after]; exact h67) p5
    (by rw [k5, hx11]) (by rw [k5, hx12])
  have F6 := F5.trans (ScanFrame.of_keep k6 sp6 m6 io6)
  by_cases cG : w.toNat = 0xF4 ∧ 0x90 ≤ x.toNat
  · rw [if_pos cG] at p6
    refine ⟨u6, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6)))), F6,
      Or.inl (pc_bad ?_ p6)⟩
    simp only [hL, utf8Scan_four _ c1 c2, cx, cy, cz, decide_eq_true cF,
      decide_eq_false (not_not_intro cG), Bool.true_and, Bool.false_and]
  rw [if_neg cG, after_after] at p6
  obtain ⟨u7, r7, p7, x97, x107, k7, sp7, m7, io7⟩ := run_next P code (c := 4) (k := 4)
    (tB := after a 4) c22 rfl (by rw [after_after]; exact h70) p6
  refine ⟨u7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))),
    F6.trans (ScanFrame.of_regs (d := 9) (e := 10) (by decide) (by decide) k7 sp7 m7 io7),
    Or.inr ⟨4, n, rfl, by omega, p7, ?_, ?_, ?_⟩⟩
  · rw [x97, k6, k5, k4 9 (by decide) (by decide), e9']
  · rw [x107, k6, k5, k4 10 (by decide) (by decide), k3 10 (by decide) (by decide),
      k2 10 (by decide) (by decide), k1, h10, ofNat_sub_ofNat (r := 4) (by omega) hr64,
      Nat.add_sub_cancel]
  · simp only [hL, utf8Scan_four _ c1 c2, cx, cy, cz, decide_eq_true cF, decide_eq_true cG,
      Bool.true_and]

/-! ## The loop -/

/-- A pass of the loop of `utf8Check` from its head at `after a 4`, with X9 at the next byte and
the `r` bytes that remain in X10. -/
theorem run_utf8Step {a bad : UInt64} {is : List Instr} (hg : utf8Check a bad = .ok is)
    (hcode : CodeAt code a is) {r : Nat} {s : State} (hpc : s.pc = after a 4)
    (hr : s.x 10 = UInt64.ofNat r) (hr64 : r < 2 ^ 64)
    (hmap : ∀ k < r, P.normal (s.x 9 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧ ScanFrame s t ∧ Utf8Pass a bad (s.x 9) s.mem r t := by
  obtain ⟨f4, f7, f9, f11, f13, f17, b20, f22, f24, f28, f32, f34, f36, f38, f40, b43, f45, f47,
    f51, f55, f59, f61, f63, f65, f67, b70, b73, h4, h7, h9, h11, h13, h17, h20, h22, h24, h28,
    h32, h34, h36, h38, h40, h43, h45, h47, h51, h55, h59, h61, h63, h65, h67, h70, h73, rfl⟩ :=
    utf8Check_ok hg
  have i4 := hcode 4 (by simp)
  have i5 := hcode 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at i4 i5
  have c6 : CodeAt code (after a 6) [.subsImm 31 11 0x80, .bcond 3 f7] := by
    simpa using CodeAt.drop_take code hcode 6 2 (by simp)
  have c8 : CodeAt code (after a 8) [.subsImm 31 11 0xC2, .bcond 3 f9] := by
    simpa using CodeAt.drop_take code hcode 8 2 (by simp)
  have c10 : CodeAt code (after a 10) [.subsImm 31 11 0xE0, .bcond 2 f11] := by
    simpa using CodeAt.drop_take code hcode 10 2 (by simp)
  have c12 : CodeAt code (after a 12) [.subsImm 31 10 2, .bcond 3 f13,
      .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f17,
      .addImm 9 9 2, .subImm 10 10 2, .b b20] := by
    simpa using CodeAt.drop_take code hcode 12 9 (by simp)
  have c21 : CodeAt code (after a 21) [.subsImm 31 11 0xF0, .bcond 2 f22] := by
    simpa using CodeAt.drop_take code hcode 21 2 (by simp)
  have c23 : CodeAt code (after a 23) [.subsImm 31 10 3, .bcond 3 f24,
      .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f28,
      .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f32,
      .subsImm 31 11 0xE0, .bcond 1 f34, .subsImm 31 12 0xA0, .bcond 3 f36,
      .subsImm 31 11 0xED, .bcond 1 f38, .subsImm 31 12 0xA0, .bcond 2 f40,
      .addImm 9 9 3, .subImm 10 10 3, .b b43] := by
    simpa using CodeAt.drop_take code hcode 23 21 (by simp)
  have c44 : CodeAt code (after a 44) [.subsImm 31 11 0xF5, .bcond 2 f45] := by
    simpa using CodeAt.drop_take code hcode 44 2 (by simp)
  have c46 : CodeAt code (after a 46) [.subsImm 31 10 4, .bcond 3 f47,
      .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 f51,
      .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f55,
      .ldrb 13 9 3, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 f59,
      .subsImm 31 11 0xF0, .bcond 1 f61, .subsImm 31 12 0x90, .bcond 3 f63,
      .subsImm 31 11 0xF4, .bcond 1 f65, .subsImm 31 12 0x90, .bcond 2 f67,
      .addImm 9 9 4, .subImm 10 10 4, .b b70] := by
    simpa using CodeAt.drop_take code hcode 46 25 (by simp)
  have c71 : CodeAt code (after a 71) [.addImm 9 9 1, .subImm 10 10 1, .b b73] := by
    simpa using CodeAt.drop_take code hcode 71 3 (by simp)
  obtain ⟨u1, r1, p1, k1, sp1, m1, io1⟩ := step_cbz P code (s := s) (r := 10)
    (target := after a 74) (by rw [hpc]; exact i4) (by rw [hpc]; exact cbField_target h4)
  have F1 : ScanFrame s u1 := ScanFrame.of_keep k1 sp1 m1 io1
  by_cases hr0 : r = 0
  · subst hr0
    rw [if_pos (show s.x 10 = 0 from hr)] at p1
    exact ⟨u1, r1, F1, Or.inl (pc_ok (by rw [readList, utf8Scan]) p1)⟩
  rw [if_neg (by rw [hr]; exact ofNat_ne_zero (by omega) hr64), hpc] at p1
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_ldrb P code (s := u1) (t := 11) (n := 9)
    (imm := 0) (by decide) (by decide) (by rw [p1, ← after_succ]; exact i5)
    (by rw [k1]; exact hmap 0 (by omega))
  have q2 : u2.pc = after a 6 := by rw [p2, p1, ← after_succ, ← after_succ]
  have hw11 : u2.x 11 = (s.mem (s.x 9)).toUInt64 := by
    rw [x2, m1, k1, show (0 : Fin 4096).val = 0 from rfl, add_ofNat_zero]
  obtain ⟨w, hw⟩ : ∃ w, s.mem (s.x 9) = w := ⟨_, rfl⟩
  rw [hw] at hw11
  have F2 := F1.trans (ScanFrame.of_regs (d := 11) (e := 11) (by decide) (by decide)
    (fun q h _ => k2 q h) sp2 m2 io2)
  have hx9 : u2.x 9 = s.x 9 := by rw [k2 9 (by decide), k1]
  have hx10 : u2.x 10 = UInt64.ofNat r := by rw [k2 10 (by decide), k1, hr]
  have hm2 : u2.mem = s.mem := by rw [m2, m1]
  obtain ⟨u3, r3, p3, k3, sp3, m3, io3⟩ := run_byteLo P code (r := 11) (imm := 0x80) (k := 0x80)
    (b := w) (tB := after a 71) (by decide) c6 rfl (by rw [after_after]; exact h7) q2 hw11
  have F3 := F2.trans (ScanFrame.of_keep k3 sp3 m3 io3)
  by_cases c1 : w.toNat < 0x80
  · rw [if_pos c1] at p3
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    obtain ⟨u4, r4, p4, x94, x104, k4, sp4, m4, io4⟩ := run_next P code (c := 1) (k := 1)
      (tB := after a 4) c71 rfl (by rw [after_after]; exact h73) p3
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), F3.trans (ScanFrame.of_regs (d := 9)
      (e := 10) (by decide) (by decide) k4 sp4 m4 io4), Or.inr ⟨1, n, rfl, by omega, p4, ?_, ?_,
      ?_⟩⟩
    · rw [x94, k3, hx9]
    · rw [x104, k3, hx10, ofNat_sub_ofNat (r := 1) (by omega) hr64, Nat.add_sub_cancel]
    · rw [readList_one, hw, utf8Scan_one _ c1]
  rw [if_neg c1, after_after] at p3
  obtain ⟨u4, r4, p4, k4, sp4, m4, io4⟩ := run_byteLo P code (r := 11) (imm := 0xC2) (k := 0xC2)
    (b := w) (tB := bad) (by decide) c8 rfl (by rw [after_after]; exact h9) p3 (by rw [k3, hw11])
  have F4 := F3.trans (ScanFrame.of_keep k4 sp4 m4 io4)
  by_cases c2 : w.toNat < 0xC2
  · rw [if_pos c2] at p4
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    refine ⟨u4, r1.trans (r2.trans (r3.trans r4)), F4, Or.inl (pc_bad ?_ p4)⟩
    rw [readList_one, hw, utf8Scan_low _ (by omega) c2]
  rw [if_neg c2, after_after] at p4
  obtain ⟨u5, r5, p5, k5, sp5, m5, io5⟩ := run_byteHs P code (r := 11) (imm := 0xE0) (k := 0xE0)
    (b := w) (tB := after a 21) (by decide) c10 rfl (by rw [after_after]; exact h11) p4
    (by rw [k4, k3, hw11])
  have F5 := F4.trans (ScanFrame.of_keep k5 sp5 m5 io5)
  have e9 : u5.x 9 = s.x 9 := by rw [k5, k4, k3, hx9]
  have e10 : u5.x 10 = UInt64.ofNat r := by rw [k5, k4, k3, hx10]
  have e11 : u5.x 11 = w.toUInt64 := by rw [k5, k4, k3, hw11]
  have em : u5.mem = s.mem := by rw [m5, m4, m3, hm2]
  by_cases c3 : 0xE0 ≤ w.toNat
  swap
  · rw [if_neg c3, after_after] at p5
    obtain ⟨t, rt, Ft, Pt⟩ := run_utf8Two P code (w := w) (p := s.x 9) c12 h13 h17 h20 p5 e9 e10
      hr64 hmap (by rw [em]; exact hw) (by omega) (by omega) (by omega)
    rw [em] at Pt
    exact ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans rt)))), F5.trans Ft, Pt⟩
  rw [if_pos c3] at p5
  obtain ⟨u6, r6, p6, k6, sp6, m6, io6⟩ := run_byteHs P code (r := 11) (imm := 0xF0) (k := 0xF0)
    (b := w) (tB := after a 44) (by decide) c21 rfl (by rw [after_after]; exact h22) p5 e11
  have F6 := F5.trans (ScanFrame.of_keep k6 sp6 m6 io6)
  by_cases c4 : 0xF0 ≤ w.toNat
  swap
  · rw [if_neg c4, after_after] at p6
    obtain ⟨t, rt, Ft, Pt⟩ := run_utf8Three P code (w := w) (p := s.x 9) c23 h24 h28 h32 h34 h36
      h38 h40 h43 p6
      (by rw [k6, e9]) (by rw [k6, e10]) (by rw [k6, e11]) hr64 hmap (by rw [m6, em]; exact hw)
      (by omega) c3 (by omega)
    rw [m6, em] at Pt
    exact ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans rt))))), F6.trans Ft,
      Pt⟩
  rw [if_pos c4] at p6
  obtain ⟨u7, r7, p7, k7, sp7, m7, io7⟩ := run_byteHs P code (r := 11) (imm := 0xF5) (k := 0xF5)
    (b := w) (tB := bad) (by decide) c44 rfl (by rw [after_after]; exact h45) p6
    (by rw [k6, e11])
  have F7 := F6.trans (ScanFrame.of_keep k7 sp7 m7 io7)
  by_cases c5 : 0xF5 ≤ w.toNat
  · rw [if_pos c5] at p7
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    refine ⟨u7, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans r7))))), F7,
      Or.inl (pc_bad ?_ p7)⟩
    rw [readList_one, hw, utf8Scan_high _ c5]
  rw [if_neg c5, after_after] at p7
  obtain ⟨t, rt, Ft, Pt⟩ := run_utf8Four P code (w := w) (p := s.x 9) c46 h47 h51 h55 h59 h61 h63
    h65 h67 h70 p7
    (by rw [k7, k6, e9]) (by rw [k7, k6, e10]) (by rw [k7, k6, e11]) hr64 hmap
    (by rw [m7, m6, em]; exact hw) (by omega) c4 (by omega)
  rw [m7, m6, em] at Pt
  exact ⟨t, r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans rt)))))),
    F7.trans Ft, Pt⟩

/-- The loop of `utf8Check` from its head at `after a 4`, with X9 at the next byte and the `r`
bytes that remain in X10. -/
theorem run_utf8Loop {a bad : UInt64} {is : List Instr} (hg : utf8Check a bad = .ok is)
    (hcode : CodeAt code a is) :
    ∀ (r : Nat) (s : State), s.pc = after a 4 → s.x 10 = UInt64.ofNat r → r < 2 ^ 64 →
      (∀ k < r, P.normal (s.x 9 + UInt64.ofNat k) = true) →
      ∃ t, Reach P code s t ∧ ScanFrame s t ∧
        t.pc = if utf8Scan (readList s.mem (s.x 9) r) then after a 74 else bad := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s hpc hr hr64 hmap
  obtain ⟨u, ru, Fu, hu | ⟨c, r', hrc, hc, hpu, h9, h10, hscan⟩⟩ :=
    run_utf8Step P code hg hcode hpc hr hr64 hmap
  · exact ⟨u, ru, Fu, hu⟩
  obtain ⟨t, rt, Ft, ht⟩ := ih r' (by omega) u hpu h10 (by omega) (fun k hk => by
    rw [h9, add_ofNat_add]
    exact hmap (c + k) (by omega))
  refine ⟨t, ru.trans rt, Fu.trans Ft, ?_⟩
  rw [ht, h9, Fu.mem, hscan]

/-! ## The check -/

/-- The run of `utf8Check` from its first word: the next word after it when the `n` bytes from
the guest's address `X17 + 4096 + X2`, `n` in X3, are UTF-8 by `utf8Scan`, and `bad` otherwise,
with X9 to X13 changed. -/
theorem run_utf8Check {a bad : UInt64} {is : List Instr} (hg : utf8Check a bad = .ok is)
    (hcode : CodeAt code a is) {s : State} (hpc : s.pc = a)
    (hmap : ∀ k < (s.x 3).toNat,
      P.normal (s.x 17 + UInt64.ofNat 4096 + s.x 2 + UInt64.ofNat k) = true) :
    ∃ t, Reach P code s t ∧
      t.pc = (if utf8Scan (readList s.mem (s.x 17 + UInt64.ofNat 4096 + s.x 2) (s.x 3).toNat)
        then after a 74 else bad) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 11 → q ≠ 12 → q ≠ 13 → t.x q = s.x q) ∧
      t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ :=
    utf8Check_ok hg
  have i0 := hcode 0 (by simp)
  have i1 := hcode 1 (by simp)
  have i2 := hcode 2 (by simp)
  have i3 := hcode 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at i0 i1 i2 i3
  obtain ⟨u1, r1, p1, x1, k1, sp1, m1, io1⟩ := step_addReg P code (s := s) (d := 9) (n := 17)
    (m := 2) (by decide) (by rw [hpc]; exact i0)
  have q1 : u1.pc = after a 1 := by rw [p1, hpc, after_one]
  obtain ⟨u2, r2, p2, x2, k2, sp2, m2, io2⟩ := step_addImm P code (s := u1) (d := 9) (n := 9)
    (imm := 4095) (by decide) (by decide) (by rw [q1]; exact i1)
  have q2 : u2.pc = after a 2 := by rw [p2, q1, ← after_succ]
  obtain ⟨u3, r3, p3, x3, k3, sp3, m3, io3⟩ := step_addImm P code (s := u2) (d := 9) (n := 9)
    (imm := 1) (by decide) (by decide) (by rw [q2]; exact i2)
  have q3 : u3.pc = after a 3 := by rw [p3, q2, ← after_succ]
  obtain ⟨u4, r4, p4, x4, k4, sp4, m4, io4⟩ := step_mov P code (s := u3) (d := 10) (m := 3)
    (by decide) (by rw [q3]; exact i3)
  have q4 : u4.pc = after a 4 := by rw [p4, q3, ← after_succ]
  have hG : u4.x 9 = s.x 17 + UInt64.ofNat 4096 + s.x 2 := by
    rw [k4 9 (by decide), x3, x2, x1]
    show s.x 17 + s.x 2 + UInt64.ofNat 4095 + UInt64.ofNat 1 = _
    have := (s.x 17).toNat_lt
    have := (s.x 2).toNat_lt
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMod] at *
    omega
  have hN : u4.x 10 = UInt64.ofNat (s.x 3).toNat := by
    rw [x4, k3 3 (by decide), k2 3 (by decide), k1 3 (by decide), UInt64.ofNat_toNat]
  obtain ⟨t, rt, Ft, pt⟩ := run_utf8Loop P code hg hcode (s.x 3).toNat u4 q4 hN
    (s.x 3).toNat_lt (fun k hk => by rw [hG]; exact hmap k hk)
  rw [hG, m4, m3, m2, m1] at pt
  refine ⟨t, r1.trans (r2.trans (r3.trans (r4.trans rt))), pt,
    fun q h9 h10 h11 h12 h13 => ?_, by rw [Ft.sp, sp4, sp3, sp2, sp1],
    by rw [Ft.mem, m4, m3, m2, m1], by rw [Ft.io, io4, io3, io2, io1]⟩
  rw [Ft.regs q h9 h10 h11 h12 h13, k4 q h10, k3 q h9, k2 q h9, k1 q h9]

end LeanExe.A64
