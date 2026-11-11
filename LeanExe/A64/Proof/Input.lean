import LeanExe.A64.Proof.ProgramRuns

/-!
The run of the entry routine of `genInMain`, which reads words from the PL011's receiver.
`run_readByte` follows the reads of one byte: by induction on the number of reads of UARTFR that
find RXFE set, the poll loop reaches the read of UARTDR, and the byte's word then either carries
an error flag, which branches to the stub of status 65, or adds its byte, shifted to its place, to
the word in its register.  `run_readBytes` and `run_readWords` compose the bytes of the words, the
first flagged byte ending the run at the stub.  The arithmetic of the receiver's values reads the
bits with `Nat.testBit` and uses no bit-vector decision procedure.
-/

namespace LeanExe.A64

open Wasm

/-! ## Bits of the receiver's registers -/

theorem nat_or16_and16 (x : Nat) : (x ||| 16) &&& 16 = 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow]
  cases x.testBit i <;> simp

theorem nat_clear16_and16 (x : Nat) : (x &&& 4294967279) &&& 16 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.testBit_and, Nat.testBit_and, Nat.testBit_two_pow,
    Nat.zero_testBit]
  by_cases h : 4 = i
  · subst h
    have e : Nat.testBit 4294967279 4 = false := by decide
    rw [e]
    simp
  · simp [h]

/-- The `AND` of a read of UARTFR with 0x10: 0x10 while RXFE is set, and 0 once it is clear. -/
theorem fr_and (rx : Rx) (j i : Nat) :
    (rx.fr j i).toUInt64 &&& 0x10 = if i < rx.wait j then 0x10 else 0 := by
  apply UInt64.toNat_inj.mp
  by_cases h : i < rx.wait j
  · simp only [Rx.fr, ite_eq_left h, UInt64.toNat_and, UInt32.toNat_toUInt64, UInt32.toNat_or,
      UInt64.reduceToNat, UInt32.reduceToNat]
    exact nat_or16_and16 _
  · simp only [Rx.fr, ite_eq_right h, UInt64.toNat_and, UInt32.toNat_toUInt64, UInt32.toNat_and,
      UInt64.reduceToNat, UInt32.reduceToNat]
    exact nat_clear16_and16 _

theorem nat_and_f00 (x : Nat) : x &&& 3840 = x / 256 % 16 * 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (3840 : Nat) = (2 ^ 4 - 1) * 2 ^ 8 from rfl, show (256 : Nat) = 2 ^ 8 from rfl,
    show (16 : Nat) = 2 ^ 4 from rfl, Nat.testBit_and, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 8 ≤ i
  · rw [Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

/-- The `AND` of a word of UARTDR with 0xF00, the error flags, is 0 exactly when no flag is
set. -/
theorem word_flags (w : UInt32) : w.toUInt64 &&& 0xF00 = 0 ↔ w.toNat / 256 % 16 = 0 := by
  have h := nat_and_f00 w.toNat
  constructor
  · intro e
    have := congrArg UInt64.toNat e
    simp only [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.reduceToNat] at this
    omega
  · intro e
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.reduceToNat]
    omega

/-- The `AND` of a word of UARTDR with 0xFF is its byte. -/
theorem word_byte (w : UInt32) : (w.toUInt64 &&& 0xFF).toNat = w.toNat % 256 := by
  simp only [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.reduceToNat]
  simpa using Nat.and_two_pow_sub_one_eq_mod w.toNat 8

theorem ne_add_18 (u : UInt64) : u ≠ u + 0x18 := by
  intro h
  have e := congrArg UInt64.toNat h
  rw [UInt64.toNat_add] at e
  have := u.toNat_lt
  simp only [UInt64.reduceToNat] at e
  omega

/-! ## The loads of the UART's registers -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- A 32-bit load of UARTFR returns the value of the poll in progress and counts it. -/
theorem exec_ldrW_fr {s : State} {t n : Fin 32} {imm : Fin 4096} (hn : n.val < 31)
    (ha : s.x n + UInt64.ofNat (4 * imm.val) = P.uart + 0x18) :
    exec P (.ldrW t n imm) s = some { s.devRead t (P.rx.fr s.io.rxNext s.io.rxPolls) with
      io := { s.io with rxPolls := s.io.rxPolls + 1 } } := by
  have hsp : s.spAligned n = true := by simp [State.spAligned, show n.val ≠ 31 by omega]
  simp only [exec, State.xsp_eq_x hn, ha, hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- A 32-bit load of UARTDR after a poll that found RXFE clear returns the byte's word and moves
to the next byte. -/
theorem exec_ldrW_dr {s : State} {t n : Fin 32} {imm : Fin 4096} (hn : n.val < 31)
    (ha : s.x n + UInt64.ofNat (4 * imm.val) = P.uart)
    (hw : P.rx.wait s.io.rxNext < s.io.rxPolls) :
    exec P (.ldrW t n imm) s = some { s.devRead t (P.rx.word s.io.rxNext) with
      io := { s.io with rxNext := s.io.rxNext + 1, rxPolls := 0 } } := by
  have hsp : s.spAligned n = true := by simp [State.spAligned, show n.val ≠ 31 by omega]
  have hne : ¬ P.uart = P.uart + 0x18 := ne_add_18 _
  simp only [exec, State.xsp_eq_x hn, ha, hsp, hne, hw, Bool.not_true, Bool.false_eq_true,
    and_self, ↓reduceIte]

/-- One pass of the poll loop of `readByte` at `a`, from the load of UARTFR to the `CBNZ`: X10
holds 0x10 while RXFE is set and 0 once it is clear, and the count of polls rises by 1. -/
theorem run_pollOnce {a : UInt64}
    (c1 : code (after a 1) = some (encode (.ldrW 9 8 6)))
    (c2 : code (after a 2) = some (encode (.andReg 10 9 11))) {s : State}
    (hpc : s.pc = after a 1) (h8 : s.x 8 = P.uart) (h11 : s.x 11 = 0x10) :
    ∃ u, Reach P code s u ∧ u.pc = after a 3 ∧
      u.x 10 = (if s.io.rxPolls < P.rx.wait s.io.rxNext then 0x10 else 0) ∧
      u.io = { s.io with rxPolls := s.io.rxPolls + 1 } ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → u.x q = s.x q) ∧ u.sp = s.sp ∧ u.mem = s.mem := by
  let v : UInt32 := P.rx.fr s.io.rxNext s.io.rxPolls
  let s1 : State := { s.devRead 9 v with io := { s.io with rxPolls := s.io.rxPolls + 1 } }
  have e1 : exec P (.ldrW 9 8 6) s = some s1 := exec_ldrW_fr P (by decide) (by rw [h8]; rfl)
  have hx1 : ∀ q : Fin 32, q ≠ 9 → s1.x q = s.x q := fun q hq => by
    show (s.setX 9 v.toUInt64).x q = _
    exact State.x_setX_ne (Ne.symm hq)
  have h91 : s1.x 9 = v.toUInt64 := by
    show (s.setX 9 v.toUInt64).x 9 = _
    exact State.x_setX_same (by decide)
  let w2 : UInt64 := s1.x 9 &&& s1.x 11
  let s2 : State := { s1.setX 10 w2 with pc := s1.pc + 4 }
  have e2 : exec P (.andReg 10 9 11) s1 = some s2 := rfl
  have p1 : s1.pc = after a 2 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  refine ⟨s2, reach_exec P code (by rw [hpc]; exact c1) e1
      (reach_exec P code (by rw [p1]; exact c2) e2 (.refl _)),
    by show s1.pc + 4 = _; rw [p1, ← after_succ], ?_, State.setX_io (s := s1) (r := 10) (v := w2),
    fun q h9 h10 => ?_,
    (State.setX_sp (s := s1) (r := 10) (v := w2)).trans
      (State.setX_sp (s := s) (r := 9) (v := v.toUInt64)),
    (State.setX_mem (s := s1) (r := 10) (v := w2)).trans
      (State.setX_mem (s := s) (r := 9) (v := v.toUInt64))⟩
  · show (s1.setX 10 w2).x 10 = _
    rw [State.x_setX_same (by decide)]
    show s1.x 9 &&& s1.x 11 = _
    rw [h91, hx1 11 (by decide), h11, fr_and]
  · show (s1.setX 10 w2).x q = _
    rw [State.x_setX_ne (Ne.symm h10), hx1 q h9]

/-- The poll loop of `readByte` at `a`: from the load of UARTFR after `wait j - d` polls of byte
`j`, the run reaches the load of UARTDR after `wait j + 1` polls, changing X9, X10, and the count
of polls alone. -/
theorem run_poll {a : UInt64} {back : Fin 524288}
    (c1 : code (after a 1) = some (encode (.ldrW 9 8 6)))
    (c2 : code (after a 2) = some (encode (.andReg 10 9 11)))
    (c3 : code (after a 3) = some (encode (.cbnz 10 back)))
    (hb : cbField (after a 3) (after a 1) = .ok back) :
    ∀ d (s : State), s.pc = after a 1 → s.x 8 = P.uart → s.x 11 = 0x10 →
      s.io.rxPolls + d = P.rx.wait s.io.rxNext →
      ∃ t, Reach P code s t ∧ t.pc = after a 4 ∧
        t.io = { s.io with rxPolls := P.rx.wait s.io.rxNext + 1 } ∧
        (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem := by
  intro d
  induction d with
  | zero =>
    intro s hpc h8 h11 hd
    obtain ⟨u, ru, pu, xu, iou, ku, spu, memu⟩ := run_pollOnce P code c1 c2 hpc h8 h11
    rw [ite_eq_right (by omega)] at xu
    refine ⟨{ u with pc := u.pc + 4 },
      ru.trans (reach_exec P code (by rw [pu]; exact c3) (cbnz_next P xu) (.refl _)),
      by show u.pc + 4 = _; rw [pu, ← after_succ], ?_, ku, spu, memu⟩
    show u.io = _
    rw [iou, show s.io.rxPolls + 1 = P.rx.wait s.io.rxNext + 1 by omega]
  | succ d ih =>
    intro s hpc h8 h11 hd
    obtain ⟨u, ru, pu, xu, iou, ku, spu, memu⟩ := run_pollOnce P code c1 c2 hpc h8 h11
    rw [ite_eq_left (by omega)] at xu
    have r1 : Reach P code s { u with pc := after a 1 } :=
      ru.trans (cbnz_taken P code (by rw [pu]; exact c3) pu hb (by rw [xu]; decide))
    obtain ⟨t, rt, pt, iot, xt, spt, memt⟩ := ih { u with pc := after a 1 } rfl
      (by rw [show ({ u with pc := after a 1 } : State).x 8 = u.x 8 from rfl,
        ku 8 (by decide) (by decide), h8])
      (by rw [show ({ u with pc := after a 1 } : State).x 11 = u.x 11 from rfl,
        ku 11 (by decide) (by decide), h11])
      (by show u.io.rxPolls + d = P.rx.wait u.io.rxNext; rw [iou]; dsimp only; omega)
    refine ⟨t, r1.trans rt, pt, ?_, fun q h9 h10 => (xt q h9 h10).trans (ku q h9 h10),
      spt.trans spu, memt.trans memu⟩
    rw [iot]
    show ({ u.io with rxPolls := P.rx.wait u.io.rxNext + 1 } : Io) = _
    rw [iou]


theorem State.x_devRead (s : State) (t q : Fin 32) (v : UInt32) (i : Io) :
    ({ s.devRead t v with io := i } : State).x q = (s.setX t v.toUInt64).x q := rfl

theorem byte_and (x : UInt64) : (x &&& 0xFF).toNat = x.toNat % 256 := by
  simp only [UInt64.toNat_and, UInt64.reduceToNat]
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 8

/-- The load of UARTDR and the test of its error flags, instructions 4 to 6 of `readByte`'s code
at `a`, after a poll that found RXFE clear.  When the byte's word carries no error flag, the run
reaches instruction 7 with the word in X9, X9 and X10 alone changed, and the next byte.  When it
carries one, the run reaches `err` with the output kept. -/
theorem run_dataRead {a err : UInt64} {fail : Fin 524288}
    (c4 : code (after a 4) = some (encode (.ldrW 9 8 0)))
    (c5 : code (after a 5) = some (encode (.andReg 10 9 12)))
    (c6 : code (after a 6) = some (encode (.cbnz 10 fail)))
    (hb : cbField (after a 6) err = .ok fail)
    {s : State} (hpc : s.pc = after a 4) (h8 : s.x 8 = P.uart) (h12 : s.x 12 = 0xF00)
    (hw : P.rx.wait s.io.rxNext < s.io.rxPolls) :
    (¬ P.rx.Flagged s.io.rxNext → ∃ t, Reach P code s t ∧ t.pc = after a 7 ∧
      t.x 9 = (P.rx.word s.io.rxNext).toUInt64 ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = { s.io with rxNext := s.io.rxNext + 1, rxPolls := 0 }) ∧
    (P.rx.Flagged s.io.rxNext →
      ∃ t, Reach P code s t ∧ t.pc = err ∧ t.io.out = s.io.out) := by
  let v : UInt32 := P.rx.word s.io.rxNext
  let i1 : Io := { s.io with rxNext := s.io.rxNext + 1, rxPolls := 0 }
  let s1 : State := { s.devRead 9 v with io := i1 }
  have e1 : exec P (.ldrW 9 8 0) s = some s1 :=
    exec_ldrW_dr P (by decide) (by rw [h8]; exact add_ofNat_zero _) hw
  have p1 : s1.pc = after a 5 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  have h91 : s1.x 9 = v.toUInt64 :=
    (State.x_devRead s 9 9 v i1).trans (State.x_setX_same (by decide))
  have hx1 : ∀ q : Fin 32, q ≠ 9 → s1.x q = s.x q := fun q hq =>
    (State.x_devRead s 9 q v i1).trans (State.x_setX_ne (Ne.symm hq))
  let w2 : UInt64 := s1.x 9 &&& s1.x 12
  let s2 : State := { s1.setX 10 w2 with pc := s1.pc + 4 }
  have e2 : exec P (.andReg 10 9 12) s1 = some s2 := rfl
  have p2 : s2.pc = after a 6 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have h102 : s2.x 10 = v.toUInt64 &&& 0xF00 := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
    show s1.x 9 &&& s1.x 12 = _
    rw [h91, hx1 12 (by decide), h12]
  have hx2 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → s2.x q = s.x q := fun q h9 h10 => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h10), hx1 q h9]
  have io2 : s2.io = i1 := State.setX_io (s := s1) (r := 10) (v := w2)
  have r2 : Reach P code s s2 := reach_exec P code (by rw [hpc]; exact c4) e1
    (reach_exec P code (by rw [p1]; exact c5) e2 (.refl _))
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · have h0 : s2.x 10 = 0 := by
      rw [h102]
      exact (word_flags (P.rx.word s.io.rxNext)).mpr (by unfold Rx.Flagged at hf; omega)
    refine ⟨{ s2 with pc := s2.pc + 4 },
      r2.trans (reach_exec P code (by rw [p2]; exact c6) (cbnz_next P h0) (.refl _)),
      by show s2.pc + 4 = _; rw [p2, ← after_succ], ?_, fun q h9 h10 => ?_,
      (State.setX_sp (s := s1) (r := 10) (v := w2)).trans
        (State.setX_sp (s := s) (r := 9) (v := v.toUInt64)),
      (State.setX_mem (s := s1) (r := 10) (v := w2)).trans
        (State.setX_mem (s := s) (r := 9) (v := v.toUInt64)), io2⟩
    · rw [State.x_withPc, State.x_withPc, State.x_setX_ne (by decide), h91]
    · rw [State.x_withPc]
      exact hx2 q h9 h10
  · have h0 : s2.x 10 ≠ 0 := by
      rw [h102]
      intro e
      exact hf ((word_flags (P.rx.word s.io.rxNext)).mp e)
    exact ⟨{ s2 with pc := err }, r2.trans (cbnz_taken P code (by rw [p2]; exact c6) p2 hb h0),
      rfl, by show s2.io.out = _; rw [io2]⟩

/-- The insertion of the byte of X9 into register `r`, below 8, instructions 7 to 9 of
`readByte`'s code at `a` for byte `b`, below 8, with 0xFF in X13 and `8 * b` in X14: the run
reaches instruction 10 with the byte, shifted by `8 * b` bits, ORed into `r`, and X9 and `r`
alone changed. -/
theorem run_insert {a : UInt64} {r : Fin 32} {b : Nat}
    (c7 : code (after a 7) = some (encode (.andReg 9 9 13)))
    (c8 : code (after a 8) = some (encode (.lslv 9 9 14)))
    (c9 : code (after a 9) = some (encode (.orrReg r r 9)))
    (hr : r.val < 8) (hb8 : b < 8) {s : State} (hpc : s.pc = after a 7) (h13 : s.x 13 = 0xFF)
    (h14 : s.x 14 = UInt64.ofNat (8 * b % 65536) <<< UInt64.ofNat (16 * (0 : Fin 4).val)) :
    ∃ t, Reach P code s t ∧ t.pc = after a 10 ∧
      (t.x r).toNat = (s.x r).toNat ||| (s.x 9).toNat % 256 * 2 ^ (8 * b) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ r → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧
      t.io = s.io := by
  have hr9 : r ≠ 9 := fun e => by subst e; simp at hr
  have hr31 : r.val < 31 := by omega
  let w1 : UInt64 := s.x 9 &&& s.x 13
  let s1 : State := { s.setX 9 w1 with pc := s.pc + 4 }
  have e1 : exec P (.andReg 9 9 13) s = some s1 := rfl
  let w2 : UInt64 := s1.x 9 <<< (s1.x 14 % 64)
  let s2 : State := { s1.setX 9 w2 with pc := s1.pc + 4 }
  have e2 : exec P (.lslv 9 9 14) s1 = some s2 := rfl
  let w3 : UInt64 := s2.x r ||| s2.x 9
  let s3 : State := { s2.setX r w3 with pc := s2.pc + 4 }
  have e3 : exec P (.orrReg r r 9) s2 = some s3 := rfl
  have p1 : s1.pc = after a 8 := by
    show s.pc + 4 = _
    rw [hpc, ← after_succ]
  have p2 : s2.pc = after a 9 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have h91 : (s1.x 9).toNat = (s.x 9).toNat % 256 := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
    show (s.x 9 &&& s.x 13).toNat = _
    rw [h13]
    exact byte_and _
  have h141 : s1.x 14 % 64 = UInt64.ofNat (8 * b) := by
    rw [State.x_withPc, State.x_setX_ne (by decide), h14]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
      UInt64.reduceToNat, Fin.val_zero, Nat.mul_zero, Nat.zero_mod, Nat.shiftLeft_zero,
      Nat.reducePow]
    omega
  have h92 : (s2.x 9).toNat = (s.x 9).toNat % 256 * 2 ^ (8 * b) := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
    show (s1.x 9 <<< (s1.x 14 % 64)).toNat = _
    rw [h141, UInt64.toNat_shiftLeft, h91, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
    have hb : 8 * b % 2 ^ 64 % 64 = 8 * b := by omega
    rw [hb]
    have hw : (s.x 9).toNat % 256 < 256 := Nat.mod_lt _ (by decide)
    have hp2 : 2 ^ (8 * b) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
    apply Nat.mod_eq_of_lt
    calc (s.x 9).toNat % 256 * 2 ^ (8 * b) < 256 * 2 ^ 56 :=
          Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hw (Nat.two_pow_pos _))
            (Nat.mul_le_mul_left 256 hp2)
      _ = 2 ^ 64 := by decide
  have hx2 : ∀ q : Fin 32, q ≠ 9 → s2.x q = s.x q := fun q h9 => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm h9), State.x_withPc,
      State.x_setX_ne (Ne.symm h9)]
  refine ⟨s3, reach_exec P code (by rw [hpc]; exact c7) e1
      (reach_exec P code (by rw [p1]; exact c8) e2
        (reach_exec P code (by rw [p2]; exact c9) e3 (.refl _))),
    by show s2.pc + 4 = _; rw [p2, ← after_succ], ?_, fun q h9 hq => ?_,
    (State.setX_sp (s := s2) (r := r) (v := w3)).trans ((State.setX_sp (s := s1) (r := 9)
      (v := w2)).trans (State.setX_sp (s := s) (r := 9) (v := w1))),
    (State.setX_mem (s := s2) (r := r) (v := w3)).trans ((State.setX_mem (s := s1) (r := 9)
      (v := w2)).trans (State.setX_mem (s := s) (r := 9) (v := w1))),
    (State.setX_io (s := s2) (r := r) (v := w3)).trans ((State.setX_io (s := s1) (r := 9)
      (v := w2)).trans (State.setX_io (s := s) (r := 9) (v := w1)))⟩
  · rw [State.x_withPc, State.x_setX_same hr31]
    show (s2.x r ||| s2.x 9).toNat = _
    rw [UInt64.toNat_or, h92, hx2 r hr9]
  · rw [State.x_withPc, State.x_setX_ne (Ne.symm hq), hx2 q h9]

/-- The reads of byte `b`, below 8, by `readByte` at `a` into register `r`, below 8, from a state
whose next byte is `j` with no poll of it done.  When the byte's word carries no error flag, the
run reaches the code after the reads with the byte, shifted by `8 * b` bits, ORed into `r`, the
next byte `j + 1`, and X9, X10, X14, and `r` alone changed.  When it carries one, the run reaches
`err` with the output kept. -/
theorem run_readByte {a err : UInt64} {r : Fin 32} {b : Nat} {is : List Instr}
    (hg : readByte a err r b = .ok is) (hc : CodeAt code a is) (hr : r.val < 8) (hb8 : b < 8)
    {s : State} (hpc : s.pc = a) (h8 : s.x 8 = P.uart) (h11 : s.x 11 = 0x10)
    (h12 : s.x 12 = 0xF00) (h13 : s.x 13 = 0xFF) (hp : s.io.rxPolls = 0) :
    (¬ P.rx.Flagged s.io.rxNext → ∃ t, Reach P code s t ∧ t.pc = after a 10 ∧
      (t.x r).toNat = (s.x r).toNat ||| (P.rx.word s.io.rxNext).toNat % 256 * 2 ^ (8 * b) ∧
      (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → q ≠ r → t.x q = s.x q) ∧ t.sp = s.sp ∧
      t.mem = s.mem ∧ t.io = { s.io with rxNext := s.io.rxNext + 1, rxPolls := 0 }) ∧
    (P.rx.Flagged s.io.rxNext →
      ∃ t, Reach P code s t ∧ t.pc = err ∧ t.io.out = s.io.out) := by
  unfold readByte at hg
  cases hb1 : cbField (after a 3) (after a 1) with
  | error e => simp [hb1, bind, Except.bind] at hg
  | ok back =>
  cases hb2 : cbField (after a 6) err with
  | error e => simp [hb1, hb2, bind, Except.bind] at hg
  | ok fail =>
  simp only [hb1, hb2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
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
  have hr9 : r ≠ 9 := fun e => by subst e; simp at hr
  have hr10 : r ≠ 10 := fun e => by subst e; simp at hr
  have hr14 : r ≠ 14 := fun e => by subst e; simp at hr
  -- X14 ← 8 * b
  let v14 : UInt64 := UInt64.ofNat (8 * b % 65536) <<< UInt64.ofNat (16 * (0 : Fin 4).val)
  let s1 : State := { s.setX 14 v14 with pc := s.pc + 4 }
  have e1 : exec P (.movz 14 ⟨8 * b % 65536, Nat.mod_lt _ (by decide)⟩ 0) s = some s1 := rfl
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have hx1 : ∀ q : Fin 32, q ≠ 14 → s1.x q = s.x q := fun q hq => by
    rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
  have h141 : s1.x 14 = v14 := by
    rw [State.x_withPc, State.x_setX_same (by decide)]
  -- the poll loop
  obtain ⟨s2, r2, p2, io2, x2, sp2, mem2⟩ := run_poll P code c1 c2 c3 hb1
    (P.rx.wait s.io.rxNext) s1 p1 (by rw [hx1 8 (by decide), h8])
    (by rw [hx1 11 (by decide), h11])
    (by show s.io.rxPolls + P.rx.wait s.io.rxNext = P.rx.wait s.io.rxNext; rw [hp]; omega)
  have io2' : s2.io = { s.io with rxPolls := P.rx.wait s.io.rxNext + 1 } := io2
  have hx2 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → s2.x q = s.x q := fun q h9 h10 h14 => by
    rw [x2 q h9 h10, hx1 q h14]
  have hj2 : s2.io.rxNext = s.io.rxNext := by rw [io2']
  have hp2 : s2.io.rxPolls = P.rx.wait s.io.rxNext + 1 := by rw [io2']
  have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0) e1 (.refl _)
  obtain ⟨hok, hflag⟩ := run_dataRead P code c4 c5 c6 hb2 p2
    (by rw [hx2 8 (by decide) (by decide) (by decide), h8])
    (by rw [hx2 12 (by decide) (by decide) (by decide), h12]) (by rw [hj2, hp2]; omega)
  rw [hj2] at hok hflag
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨s3, r3, p3, h93, x3, sp3, mem3, io3⟩ := hok hf
    obtain ⟨t, rt, pt, hxt, xt, spt, memt, iot⟩ := run_insert P code c7 c8 c9 hr hb8 p3
      (by rw [x3 13 (by decide) (by decide), hx2 13 (by decide) (by decide) (by decide), h13])
      (by rw [x3 14 (by decide) (by decide), x2 14 (by decide) (by decide), h141])
    refine ⟨t, r1.trans (r2.trans (r3.trans rt)), pt, ?_, fun q h9 h10 h14 hq => ?_,
      spt.trans (sp3.trans (sp2.trans (State.setX_sp (s := s) (r := 14) (v := v14)))),
      memt.trans (mem3.trans (mem2.trans (State.setX_mem (s := s) (r := 14) (v := v14)))), ?_⟩
    · rw [hxt, h93, x3 r hr9 hr10, hx2 r hr9 hr10 hr14, UInt32.toNat_toUInt64]
    · rw [xt q h9 hq, x3 q h9 h10, hx2 q h9 h10 h14]
    · rw [iot, io3, io2']
  · obtain ⟨t, rt, pt, ot⟩ := hflag hf
    exact ⟨t, r1.trans (r2.trans rt), pt, by rw [ot, io2']⟩


/-! ## The words of the reads -/

/-- The bytes of reads `j` to `j + c - 1`, each at its place: byte `j + t` times `2 ^ (8 * t)`. -/
def rxSum (rx : Rx) (j : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => rxSum rx j c + (rx.word (j + c)).toNat % 256 * 2 ^ (8 * c)

theorem pow_8succ (c : Nat) : 2 ^ (8 * (c + 1)) = 2 ^ (8 * c) * 256 := by
  rw [show 8 * (c + 1) = 8 * c + 8 by omega, Nat.pow_add, show (2 : Nat) ^ 8 = 256 from rfl]

theorem rxSum_lt (rx : Rx) (j : Nat) : ∀ c, rxSum rx j c < 2 ^ (8 * c)
  | 0 => by simp [rxSum]
  | c + 1 => by
      have ih := rxSum_lt rx j c
      have h1 : (rx.word (j + c)).toNat % 256 * 2 ^ (8 * c) ≤ 255 * 2 ^ (8 * c) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [rxSum, pow_8succ]
      omega

/-- Reads whose bytes are the base-256 digits of `x`, the lowest first, give `x` modulo
`2 ^ (8 * c)`. -/
theorem rxSum_digits {rx : Rx} {j x : Nat} :
    ∀ c, (∀ t < c, (rx.word (j + t)).toNat % 256 = x / 2 ^ (8 * t) % 256) →
      rxSum rx j c = x % 2 ^ (8 * c)
  | 0, _ => by simp [rxSum, Nat.mod_one]
  | c + 1, h => by
      rw [rxSum, rxSum_digits c (fun t ht => h t (by omega)), h c (by omega), pow_8succ,
        Nat.mod_mul, Nat.mul_comm (x / 2 ^ (8 * c) % 256)]

theorem length_flatMap_bytesOf : ∀ ws : List UInt64, (ws.flatMap bytesOf).length = 8 * ws.length
  | [] => rfl
  | w :: ws => by
      rw [List.flatMap_cons, List.length_append, length_flatMap_bytesOf ws, List.length_cons]
      simp only [bytesOf, List.length_map, List.length_range]
      omega

/-- Byte `t` of word `i` of the bytes of words `ws`. -/
theorem getElem_flatMap_bytesOf : ∀ (ws : List UInt64) (i t : Nat) (hi : i < ws.length)
    (ht : t < 8) (h : 8 * i + t < (ws.flatMap bytesOf).length),
    (ws.flatMap bytesOf)[8 * i + t] = (bytesOf ws[i])[t]'(by simp [bytesOf]; omega)
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | w :: ws, 0, t, _, ht, h => by
      simp only [List.flatMap_cons]
      rw [List.getElem_append_left (by simp [bytesOf]; omega)]
      simp
  | w :: ws, i + 1, t, hi, ht, h => by
      simp only [List.flatMap_cons]
      rw [List.getElem_append_right (by simp [bytesOf]; omega)]
      have hi' : i < ws.length := by simp at hi; omega
      have e := getElem_flatMap_bytesOf ws i t hi' ht
        (by rw [length_flatMap_bytesOf]; omega)
      simp only [List.getElem_cons_succ]
      rw [← e]
      congr 1
      simp only [bytesOf, List.length_map, List.length_range]
      omega

/-- Byte `t` of `bytesOf w` is the base-256 digit `t` of `w`. -/
theorem bytesOf_digit (w : UInt64) {t : Nat} (ht : t < 8) :
    ((bytesOf w)[t]'(by simp [bytesOf]; omega)).toNat = w.toNat / 2 ^ (8 * t) % 256 := by
  simp only [bytesOf, List.getElem_map, List.getElem_range, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have h1 : 8 * t % 2 ^ 64 % 64 = 8 * t := by omega
  rw [h1]

/-- A receiver that delivers the bytes of words `ws`, the lowest first, without an error flag:
read `8 * i + t` holds byte `t` of word `i` and no flag. -/
theorem delivers_words {rx : Rx} {ws : List UInt64} (hd : rx.Delivers (ws.flatMap bytesOf))
    {i t : Nat} (hi : i < ws.length) (ht : t < 8) :
    (rx.word (8 * i + t)).toNat % 256 = ws[i].toNat / 2 ^ (8 * t) % 256 ∧
      ¬ rx.Flagged (8 * i + t) := by
  have hl : 8 * i + t < (ws.flatMap bytesOf).length := by rw [length_flatMap_bytesOf]; omega
  have h := hd (8 * i + t) hl
  rw [getElem_flatMap_bytesOf ws i t hi ht hl, bytesOf_digit _ ht] at h
  have hb : ws[i].toNat / 2 ^ (8 * t) % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold Rx.Flagged
  omega

/-! ## The code of the reads -/

theorem readByte_length {a err : UInt64} {r : Fin 32} {b : Nat} {is : List Instr}
    (hg : readByte a err r b = .ok is) : is.length = 10 := by
  unfold readByte at hg
  cases hb1 : cbField (after a 3) (after a 1) with
  | error e => simp [hb1, bind, Except.bind] at hg
  | ok back =>
  cases hb2 : cbField (after a 6) err with
  | error e => simp [hb1, hb2, bind, Except.bind] at hg
  | ok fail =>
  simp only [hb1, hb2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  subst hg
  rfl

theorem readBytes_length {err : UInt64} {r : Fin 32} :
    ∀ c b {a : UInt64} {is : List Instr}, readBytes err r a b c = .ok is → is.length = 10 * c
  | 0, b, a, is, hg => by
      simp only [readBytes, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      rfl
  | c + 1, b, a, is, hg => by
      simp only [readBytes] at hg
      cases h1 : readByte a err r b with
      | error e => simp [h1, bind, Except.bind] at hg
      | ok first =>
      cases h2 : readBytes err r (after a 10) (b + 1) c with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok rest =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      rw [List.length_append, readByte_length h1, readBytes_length c (b + 1) h2]
      omega

theorem readWords_length {err : UInt64} :
    ∀ c i {a : UInt64} {is : List Instr}, readWords err a i c = .ok is → is.length = 81 * c
  | 0, i, a, is, hg => by
      simp only [readWords, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      rfl
  | c + 1, i, a, is, hg => by
      simp only [readWords] at hg
      cases h1 : readBytes err ⟨i % 32, Nat.mod_lt _ (by decide)⟩ (after a 1) 0 8 with
      | error e => simp [h1, bind, Except.bind] at hg
      | ok bytes =>
      cases h2 : readWords err (after a 81) (i + 1) c with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok rest =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      rw [List.length_append, List.length_cons, readBytes_length 8 0 h1,
        readWords_length c (i + 1) h2]
      omega

theorem Io.eq_with {i : Io} {n p : Nat} (hn : i.rxNext = n) (hp : i.rxPolls = p) :
    i = { i with rxNext := n, rxPolls := p } := by
  cases i
  simp only at hn hp
  rw [hn, hp]

theorem ne_of_lt8 {r : Fin 32} (hr : r.val < 8) {q : Fin 32} (hq : 8 ≤ q.val) : q ≠ r :=
  fun e => by subst e; omega

/-! ## The runs of the reads -/

/-- The reads of bytes `b` to `b + c - 1` by `readBytes` at `a` into register `r`, below 8, from
a state at read `j + b` of a word whose first read is `j`, with no poll done and the word's first
`b` bytes in `r`.  When none of the bytes carries an error flag, the run reaches the code after
the reads with the word's first `b + c` bytes in `r`.  When one does after bytes without a flag,
the run reaches `err` with the output kept. -/
theorem run_readBytes {err : UInt64} {r : Fin 32} (hr : r.val < 8) (j : Nat) :
    ∀ c b {a : UInt64} {is : List Instr} {s : State}, b + c ≤ 8 →
      readBytes err r a b c = .ok is → CodeAt code a is → s.pc = a → s.x 8 = P.uart →
      s.x 11 = 0x10 → s.x 12 = 0xF00 → s.x 13 = 0xFF → s.io.rxNext = j + b →
      s.io.rxPolls = 0 → (s.x r).toNat = rxSum P.rx j b →
      ((∀ t < c, ¬ P.rx.Flagged (j + b + t)) → ∃ u, Reach P code s u ∧
        u.pc = after a (10 * c) ∧ (u.x r).toNat = rxSum P.rx j (b + c) ∧
        (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → q ≠ r → u.x q = s.x q) ∧ u.sp = s.sp ∧
        u.mem = s.mem ∧ u.io = { s.io with rxNext := j + b + c, rxPolls := 0 }) ∧
      (∀ t < c, (∀ i < t, ¬ P.rx.Flagged (j + b + i)) → P.rx.Flagged (j + b + t) →
        ∃ u, Reach P code s u ∧ u.pc = err ∧ u.io.out = s.io.out)
  | 0, b, a, is, s, _, hg, _, hpc, _, _, _, _, hj, hp, hx => by
      refine ⟨fun _ => ⟨s, .refl _, by rw [hpc, Nat.mul_zero, after_zero], hx,
        fun _ _ _ _ _ => rfl, rfl, rfl, Io.eq_with (by rw [hj, Nat.add_zero]) hp⟩,
        fun t ht => absurd ht (by omega)⟩
  | c + 1, b, a, is, s, hbc, hg, hc, hpc, h8, h11, h12, h13, hj, hp, hx => by
      simp only [readBytes] at hg
      cases h1 : readByte a err r b with
      | error e => simp [h1, bind, Except.bind] at hg
      | ok first =>
      cases h2 : readBytes err r (after a 10) (b + 1) c with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok rest =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      obtain ⟨c1, c2⟩ := CodeAt.split code hc (readByte_length h1)
      obtain ⟨hok, hflag⟩ := run_readByte P code h1 c1 hr (by omega) hpc h8 h11 h12 h13 hp
      rw [hj] at hok hflag
      have hr8 := ne_of_lt8 hr (q := 8) (by decide)
      have hr11 := ne_of_lt8 hr (q := 11) (by decide)
      have hr12 := ne_of_lt8 hr (q := 12) (by decide)
      have hr13 := ne_of_lt8 hr (q := 13) (by decide)
      -- the first byte's run, when it carries no flag, and the rest from there
      have step : ¬ P.rx.Flagged (j + b) → ∃ u, Reach P code s u ∧ u.pc = after a 10 ∧
          (u.x r).toNat = rxSum P.rx j (b + 1) ∧
          (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → q ≠ r → u.x q = s.x q) ∧ u.sp = s.sp ∧
          u.mem = s.mem ∧ u.io = { s.io with rxNext := j + b + 1, rxPolls := 0 } := by
        intro hf
        obtain ⟨u, ru, pu, xu, ku, spu, memu, iou⟩ := hok hf
        refine ⟨u, ru, pu, ?_, ku, spu, memu, iou⟩
        rw [xu, hx]
        exact or_mul_two_pow (rxSum_lt _ _ _)
      refine ⟨fun hf => ?_, fun t ht hpre hft => ?_⟩
      · obtain ⟨u, ru, pu, xu, ku, spu, memu, iou⟩ := step (by simpa using hf 0 (by omega))
        obtain ⟨hok', -⟩ := run_readBytes hr j c (b + 1) (by omega) h2 c2 pu
          (by rw [ku 8 (by decide) (by decide) (by decide) hr8, h8])
          (by rw [ku 11 (by decide) (by decide) (by decide) hr11, h11])
          (by rw [ku 12 (by decide) (by decide) (by decide) hr12, h12])
          (by rw [ku 13 (by decide) (by decide) (by decide) hr13, h13])
          ((by rw [iou] : u.io.rxNext = j + b + 1).trans (by omega)) (by rw [iou]) xu
        obtain ⟨v, rv, pv, xv, kv, spv, memv, iov⟩ := hok' fun t ht => by
          have := hf (t + 1) (by omega)
          rwa [show j + b + (t + 1) = j + (b + 1) + t by omega] at this
        refine ⟨v, ru.trans rv, ?_, ?_, fun q h9 h10 h14 hq => (kv q h9 h10 h14 hq).trans
          (ku q h9 h10 h14 hq), spv.trans spu, memv.trans memu, ?_⟩
        · rw [pv, after_after]
          congr 1
          omega
        · rw [xv, show b + 1 + c = b + (c + 1) by omega]
        · rw [iov, iou, show j + (b + 1) + c = j + b + (c + 1) by omega]
      · rcases t with _ | t
        · exact hflag (by simpa using hft)
        · obtain ⟨u, ru, pu, xu, ku, spu, memu, iou⟩ :=
            step (by simpa using hpre 0 (by omega))
          obtain ⟨-, hflag'⟩ := run_readBytes hr j c (b + 1) (by omega) h2 c2 pu
            (by rw [ku 8 (by decide) (by decide) (by decide) hr8, h8])
            (by rw [ku 11 (by decide) (by decide) (by decide) hr11, h11])
            (by rw [ku 12 (by decide) (by decide) (by decide) hr12, h12])
            (by rw [ku 13 (by decide) (by decide) (by decide) hr13, h13])
            ((by rw [iou] : u.io.rxNext = j + b + 1).trans (by omega)) (by rw [iou]) xu
          obtain ⟨v, rv, pv, ov⟩ := hflag' t (by omega)
            (fun i hi => by
              have := hpre (i + 1) (by omega)
              rwa [show j + b + (i + 1) = j + (b + 1) + i by omega] at this)
            (by rwa [show j + b + (t + 1) = j + (b + 1) + t by omega] at hft)
          exact ⟨v, ru.trans rv, pv, by rw [ov, iou]⟩

/-- The reads of words `i` to `i + c - 1` by `readWords` at `a`, each into register `i`, from a
state at read `8 * i` with no poll done.  When none of the `8 * c` bytes carries an error flag,
the run reaches the code after the reads with the sum of word `k`'s bytes in register `k`, and
registers outside those, X9, X10, and X14 kept.  When one does after bytes without a flag, the run
reaches `err` with the output kept. -/
theorem run_readWords {err : UInt64} :
    ∀ c i {a : UInt64} {is : List Instr} {s : State}, i + c ≤ 8 →
      readWords err a i c = .ok is → CodeAt code a is → s.pc = a → s.x 8 = P.uart →
      s.x 11 = 0x10 → s.x 12 = 0xF00 → s.x 13 = 0xFF → s.io.rxNext = 8 * i →
      s.io.rxPolls = 0 →
      ((∀ t < 8 * c, ¬ P.rx.Flagged (8 * i + t)) → ∃ u, Reach P code s u ∧
        u.pc = after a (81 * c) ∧
        (∀ k, i ≤ k → k < i + c →
          (u.x ⟨k % 32, Nat.mod_lt _ (by decide)⟩).toNat = rxSum P.rx (8 * k) 8) ∧
        (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → (q.val < i ∨ i + c ≤ q.val) → u.x q = s.x q) ∧
        u.sp = s.sp ∧ u.mem = s.mem ∧ u.io.out = s.io.out) ∧
      (∀ t < 8 * c, (∀ t' < t, ¬ P.rx.Flagged (8 * i + t')) → P.rx.Flagged (8 * i + t) →
        ∃ u, Reach P code s u ∧ u.pc = err ∧ u.io.out = s.io.out)
  | 0, i, a, is, s, _, hg, _, hpc, _, _, _, _, _, _ => by
      refine ⟨fun _ => ⟨s, .refl _, by rw [hpc, Nat.mul_zero, after_zero],
        fun k hk hk' => absurd hk' (by omega), fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩,
        fun t ht => absurd ht (by omega)⟩
  | c + 1, i, a, is, s, hic, hg, hc, hpc, h8, h11, h12, h13, hj, hp => by
      simp only [readWords] at hg
      cases h1 : readBytes err ⟨i % 32, Nat.mod_lt _ (by decide)⟩ (after a 1) 0 8 with
      | error e => simp [h1, bind, Except.bind] at hg
      | ok bytes =>
      cases h2 : readWords err (after a 81) (i + 1) c with
      | error e => simp [h1, h2, bind, Except.bind] at hg
      | ok rest =>
      simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
      subst hg
      let r : Fin 32 := ⟨i % 32, Nat.mod_lt _ (by decide)⟩
      have hr : r.val < 8 := by show i % 32 < 8; omega
      have hri : r.val = i := by show i % 32 = i; omega
      have hsp := CodeAt.split code hc (n := 81) (by simp [readBytes_length 8 0 h1])
      obtain ⟨c0, c1⟩ := (CodeAt.cons (code := code)).mp hsp.1
      have c2 := hsp.2
      -- MOVZ of 0 into the word's register
      let v0 : UInt64 := UInt64.ofNat (0 : Fin 65536).val <<< UInt64.ofNat (16 * (0 : Fin 4).val)
      let s1 : State := { s.setX r v0 with pc := s.pc + 4 }
      have e1 : exec P (.movz r 0 0) s = some s1 := rfl
      have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
      have hx1 : ∀ q : Fin 32, q ≠ r → s1.x q = s.x q := fun q hq => by
        rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
      have hr1 : (s1.x r).toNat = rxSum P.rx (8 * i) 0 := by
        rw [State.x_withPc, State.x_setX_same (by omega)]
        rfl
      have r1 : Reach P code s s1 := reach_exec P code (by rw [hpc]; exact c0) e1 (.refl _)
      have io1 : s1.io = s.io := State.setX_io (s := s) (r := r) (v := v0)
      have hr8 := ne_of_lt8 hr (q := 8) (by decide)
      have hr11 := ne_of_lt8 hr (q := 11) (by decide)
      have hr12 := ne_of_lt8 hr (q := 12) (by decide)
      have hr13 := ne_of_lt8 hr (q := 13) (by decide)
      obtain ⟨hok, hflag⟩ := run_readBytes P code hr (8 * i) 8 0 (by omega) h1 c1 p1
        (by rw [hx1 8 hr8, h8]) (by rw [hx1 11 hr11, h11]) (by rw [hx1 12 hr12, h12])
        (by rw [hx1 13 hr13, h13]) (by rw [io1, hj, Nat.add_zero]) (by rw [io1, hp]) hr1
      -- the first word, when its bytes carry no flag
      have step : (∀ t < 8, ¬ P.rx.Flagged (8 * i + t)) → ∃ u, Reach P code s u ∧
          u.pc = after a 81 ∧ (u.x r).toNat = rxSum P.rx (8 * i) 8 ∧
          (∀ q : Fin 32, q ≠ 9 → q ≠ 10 → q ≠ 14 → q ≠ r → u.x q = s.x q) ∧ u.sp = s.sp ∧
          u.mem = s.mem ∧ u.io.out = s.io.out ∧ u.io.rxNext = 8 * (i + 1) ∧ u.io.rxPolls = 0 := by
        intro hf
        obtain ⟨u, ru, pu, xu, ku, spu, memu, iou⟩ := hok (fun t ht => by simpa using hf t ht)
        refine ⟨u, r1.trans ru, by rw [pu, after_after], xu,
          fun q h9 h10 h14 hq => (ku q h9 h10 h14 hq).trans (hx1 q hq),
          spu.trans (State.setX_sp (s := s) (r := r) (v := v0)),
          memu.trans (State.setX_mem (s := s) (r := r) (v := v0)), ?_, ?_, ?_⟩
        · rw [iou]
          show s1.io.out = s.io.out
          rw [io1]
        · exact (by rw [iou] : u.io.rxNext = 8 * i + 0 + 8).trans (by omega)
        · rw [iou]
      refine ⟨fun hf => ?_, fun t ht hpre hft => ?_⟩
      · obtain ⟨u, ru, pu, xu, ku, spu, memu, ou, nu, pu'⟩ :=
          step fun t ht => hf t (by omega)
        obtain ⟨hok', -⟩ := run_readWords c (i + 1) (by omega) h2 c2 pu
          (by rw [ku 8 (by decide) (by decide) (by decide) hr8, h8])
          (by rw [ku 11 (by decide) (by decide) (by decide) hr11, h11])
          (by rw [ku 12 (by decide) (by decide) (by decide) hr12, h12])
          (by rw [ku 13 (by decide) (by decide) (by decide) hr13, h13]) nu pu'
        obtain ⟨v, rv, pv, xv, kv, spv, memv, ov⟩ := hok' fun t ht => by
          have := hf (8 + t) (by omega)
          rwa [show 8 * i + (8 + t) = 8 * (i + 1) + t by omega] at this
        refine ⟨v, ru.trans rv, ?_, fun k hk hk' => ?_, fun q h9 h10 h14 hq => ?_,
          spv.trans spu, memv.trans memu, ov.trans ou⟩
        · rw [pv, after_after]
          congr 1
          omega
        · rcases Nat.lt_or_ge k (i + 1) with hk1 | hk1
          · have hki : k = i := by omega
            rw [hki]
            exact (congrArg UInt64.toNat (kv r (ne_of_lt8 hr (q := 9) (by decide)).symm
              (ne_of_lt8 hr (q := 10) (by decide)).symm (ne_of_lt8 hr (q := 14) (by decide)).symm
              (.inl (by rw [hri]; omega)))).trans xu
          · exact xv k hk1 (by omega)
        · rw [kv q h9 h10 h14 (by omega)]
          exact ku q h9 h10 h14 (fun e => by subst e; omega)
      · rcases Nat.lt_or_ge t 8 with ht8 | ht8
        · obtain ⟨u, ru, pu, ou⟩ := hflag t ht8 (fun t' ht' => by simpa using hpre t' ht')
            (by simpa using hft)
          exact ⟨u, r1.trans ru, pu, ou.trans (by rw [io1])⟩
        · obtain ⟨u, ru, pu, xu, ku, spu, memu, ou, nu, pu'⟩ :=
            step fun t' ht' => hpre t' (by omega)
          obtain ⟨-, hflag'⟩ := run_readWords c (i + 1) (by omega) h2 c2 pu
            (by rw [ku 8 (by decide) (by decide) (by decide) hr8, h8])
            (by rw [ku 11 (by decide) (by decide) (by decide) hr11, h11])
            (by rw [ku 12 (by decide) (by decide) (by decide) hr12, h12])
            (by rw [ku 13 (by decide) (by decide) (by decide) hr13, h13]) nu pu'
          obtain ⟨v, rv, pv, ov⟩ := hflag' (t - 8) (by omega)
            (fun t' ht' => by
              have := hpre (8 + t') (by omega)
              rwa [show 8 * i + (8 + t') = 8 * (i + 1) + t' by omega] at this)
            (by rwa [show 8 * i + t = 8 * (i + 1) + (t - 8) by omega] at hft)
          exact ⟨v, ru.trans rv, pv, ov.trans ou⟩


/-! ## The entry routine -/

/-- `genInMain`'s code: the shape of `MainShape` around the setting of X8, X11, X12, and X13 and
the reads, with the stub of status 65 after the return. -/
theorem gen_inMain {a e uart room base : UInt64} {n : Nat} {o : Output} {main : List Instr}
    (hg : genInMain a e n uart room base o = .ok main) :
    n ≤ 8 ∧ ∃ reads exit,
      readWords (after a (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7)) (after a 15) 0 n =
        .ok reads ∧
      bField (after (after a (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7)) 4) base = .ok exit ∧
      MainShape a e (movImm 8 uart ++ [.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0] ++
        reads) (movImm 0 65 ++ [.b exit]) uart room o main := by
  unfold genInMain at hg
  by_cases hc : n > 8
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  cases hr : readWords (after a (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7)) (after a 15) 0 n with
  | error err => simp [hc, hr, bind, Except.bind] at hg
  | ok reads =>
  cases hb : bField (after a (8 + (7 + 81 * n))) e with
  | error err => simp [hc, hr, hb, bind, Except.bind] at hg
  | ok g =>
  cases ho : genOut (after a (13 + (7 + 81 * n))) o with
  | error err => simp [hc, hr, hb, ho, bind, Except.bind] at hg
  | ok out =>
  cases hx : bField (after (after a (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7)) 4) base with
  | error err => simp [hc, hr, hb, ho, hx, bind, Except.bind] at hg
  | ok exit =>
  simp [hc, hr, hb, ho, hx, bind, Except.bind, pure, Except.pure] at hg
  subst hg
  have hl : (movImm 8 uart ++ [Instr.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0] ++
      reads).length = 7 + 81 * n := by
    simp only [List.length_append, movImm_length, List.length_cons, List.length_nil,
      readWords_length n 0 hr]
  exact ⟨by omega, reads, exit, rfl, rfl, g, out, by rw [hl]; exact hb, by rw [hl]; exact ho,
    by simp⟩

/-- When some read below `N` from `j` carries an error flag, the first one does. -/
theorem exists_first_flagged (rx : Rx) (j : Nat) : ∀ N, ¬ (∀ t < N, ¬ rx.Flagged (j + t)) →
    ∃ t < N, (∀ t' < t, ¬ rx.Flagged (j + t')) ∧ rx.Flagged (j + t)
  | 0, h => absurd (fun t ht => absurd ht (by omega)) h
  | N + 1, h => by
      by_cases hN : ∀ t < N, ¬ rx.Flagged (j + t)
      · refine ⟨N, by omega, hN, Classical.byContradiction fun hF => h fun t ht => ?_⟩
        rcases Nat.lt_or_ge t N with h1 | h1
        · exact hN t h1
        · rw [show t = N by omega]
          exact hF
      · obtain ⟨t, ht, h1, h2⟩ := exists_first_flagged rx j N hN
        exact ⟨t, by omega, h1, h2⟩

/-- `MOVZ Xd` of `v` at a state's program counter: the next instruction with `d`, below 31,
holding `v` and every other register, SP, the memory, and the UART's state kept. -/
theorem run_movz {s : State} {d : Fin 32} {v : Fin 65536} (hd : d.val < 31)
    (hc : code s.pc = some (encode (.movz d v 0))) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = UInt64.ofNat v.val ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io := by
  let w : UInt64 := UInt64.ofNat v.val <<< UInt64.ofNat (16 * (0 : Fin 4).val)
  refine ⟨{ s.setX d w with pc := s.pc + 4 }, reach_exec P code hc rfl (.refl _), rfl, ?_,
    fun q hq => by rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)], State.setX_sp,
    State.setX_mem, State.setX_io⟩
  rw [State.x_withPc, State.x_setX_same hd]
  apply UInt64.toNat_inj.mp
  simp only [w, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', Fin.val_zero, Nat.mul_zero,
    Nat.zero_mod, Nat.shiftLeft_zero, Nat.mod_mod]

/-- The run of a program of `genInProgram`, which reads `n` words from the UART and runs function
`k` of `m` on them, from `main` at `after base 1` with the receiver at its first read and no poll
done: `programWith_sim` with the reads as the setup.  Either a byte among the first `8 * n`
carries an error flag and the machine reaches the exit word with status 65 and the output kept,
or no byte does, and for the words `ws` whose bytes the reads gave, the machine does what
`ProgramOutcome` states for Talos's run of the function on `argValues f.params ws`. -/
theorem inProgram_sim {m : Module} {k n : Nat} {f : Function}
    {base room area : UInt64} {cap : Nat} {o : Output} {is : List Instr}
    (hg : genInProgram m k n P.uart base room cap o = .ok is)
    (hcode : CodeAt code (after base 1) is) (hm : m.imports = []) (hk : m.funcs[k]? = some f)
    (hp : n = f.params.length) (F : Nat)
    (ms : State) (hpc : ms.pc = after base 1) (hal : ms.sp % 16 = 0)
    (hroom : 4096 ≤ room.toNat) (htop : ms.sp.toNat ≤ 2 ^ 63)
    (hstack : ∀ j < room.toNat + 16, P.normal (ms.sp - 16 - room + UInt64.ofNat j) = true)
    (h17 : ms.x 17 = area)
    (harea : ∀ j < areaSize cap, ms.mem (area + UInt64.ofNat j) = areaByte m.initialStore j)
    (hamap : ∀ j < areaSize cap, P.normal (area + UInt64.ofNat j) = true)
    (habove : area.toNat + areaSize cap + room.toNat + 16 ≤ ms.sp.toNat)
    (hrx : ms.io.rxNext = 0) (hpo : ms.io.rxPolls = 0) :
    (∃ ms', Reach P code ms ms' ∧ ms'.pc = base ∧
      (ms'.x 0 = 65 ∧ ∃ t < 8 * n, P.rx.Flagged t) ∧ ms'.io.out = ms.io.out) ∨
    ∃ ws, (ws.length = n ∧ (∀ i (hi : i < ws.length), ws[i].toNat = rxSum P.rx (8 * i) 8) ∧
        ∀ t < 8 * n, ¬ P.rx.Flagged t) ∧
      ProgramOutcome P code base (callTargets m k ≠ [] ∧ room.toNat < stackBound m k) o
        (Wasm.run F m k (initStore m cap) (argValues f.params ws).reverse) ms := by
  obtain ⟨-, -, -, -, main, -, e, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmg, -⟩ :=
    gen_programWith hg
  obtain ⟨h8, reads, exit, hr, hx, -⟩ := gen_inMain hmg
  have hl : (movImm 8 P.uart ++ [Instr.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0] ++
      reads).length = 7 + 81 * n := by
    simp only [List.length_append, movImm_length, List.length_cons, List.length_nil,
      readWords_length n 0 hr]
  refine programWith_sim P code
    (setup := movImm 8 P.uart ++ [.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0] ++ reads)
    (tail := movImm 0 65 ++ [.b exit])
    (Q := fun ws => ws.length = n ∧ (∀ i (hi : i < ws.length), ws[i].toNat = rxSum P.rx (8 * i) 8) ∧
      ∀ t < 8 * n, ¬ P.rx.Flagged t)
    (X := fun c => c = 65 ∧ ∃ t < 8 * n, P.rx.Flagged t) hg (fun e' main' hmg' => ?_)
    (by rw [hl]; simp only [inMainSize, List.length_append, movImm_length, List.length_cons,
      List.length_nil]; omega)
    hcode hm hk F ms hpc hal hroom htop hstack h17 harea hamap habove ?_
  · obtain ⟨-, reads', exit', hr', hx', hs'⟩ := gen_inMain hmg'
    rw [hr] at hr'
    rw [hx] at hx'
    cases hr'
    cases hx'
    exact hs'
  intro cs ct s hs hio
  generalize hA : after base 1 = A at *
  have cs1 := CodeAt.split code cs (n := 7) (by simp [movImm])
  have cs2 := CodeAt.split code cs1.1 (n := 4) (by simp [movImm])
  have c11 : code (after (after A 8) 4) = some (encode (.movz 11 0x10 0)) := by
    have := cs2.2 0 (by simp)
    rwa [after_zero] at this
  have c12 : code (after (after A 8) 5) = some (encode (.movz 12 0xF00 0)) := by
    have := cs2.2 1 (by simp)
    rwa [after_after] at this
  have c13 : code (after (after A 8) 6) = some (encode (.movz 13 0xFF 0)) := by
    have := cs2.2 2 (by simp)
    rwa [after_after] at this
  -- X8, X11, X12, X13
  obtain ⟨s1, r1, p1, x81, k1, sp1, mem1, io1⟩ :=
    run_movImm P code (d := 8) (v := P.uart) (by decide) cs2.1 hs
  obtain ⟨s2, r2, p2, x112, k2, sp2, mem2, io2⟩ :=
    run_movz P code (d := 11) (v := 0x10) (by decide) (by rw [p1]; exact c11)
  have p2' : s2.pc = after (after A 8) 5 := by rw [p2, p1, ← after_succ]
  obtain ⟨s3, r3, p3, x123, k3, sp3, mem3, io3⟩ :=
    run_movz P code (d := 12) (v := 0xF00) (by decide) (by rw [p2']; exact c12)
  have p3' : s3.pc = after (after A 8) 6 := by rw [p3, p2', ← after_succ]
  obtain ⟨s4, r4, p4, x134, k4, sp4, mem4, io4⟩ :=
    run_movz P code (d := 13) (v := 0xFF) (by decide) (by rw [p3']; exact c13)
  have p4'' : s4.pc = after (after A 8) 7 := by rw [p4, p3', ← after_succ]
  have p4' : s4.pc = after A 15 := by rw [p4'', after_after]
  have hk4 : ∀ q : Fin 32, q ≠ 8 → q ≠ 11 → q ≠ 12 → q ≠ 13 → s4.x q = s.x q :=
    fun q h8q h11 h12 h13 => by rw [k4 q h13, k3 q h12, k2 q h11, k1 q h8q]
  have io4' : s4.io = ms.io := by rw [io4, io3, io2, io1, hio]
  have r4' : Reach P code s s4 := r1.trans (r2.trans (r3.trans r4))
  have cr : CodeAt code (after A 15) reads := by
    have := cs1.2
    rwa [after_after] at this
  have hw := run_readWords P code (err := after A (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7))
    n 0 (by omega) hr cr p4'
    (by rw [k4 8 (by decide), k3 8 (by decide), k2 8 (by decide), x81])
    (by rw [k4 11 (by decide), k3 11 (by decide)]; exact x112)
    (by rw [k4 12 (by decide)]; exact x123) x134 ((congrArg Io.rxNext io4').trans hrx)
    ((congrArg Io.rxPolls io4').trans hpo)
  by_cases hf : ∀ t < 8 * n, ¬ P.rx.Flagged (8 * 0 + t)
  · obtain ⟨u, ru, pu, xu, ku, spu, memu, ou⟩ := hw.1 hf
    refine .inl ⟨List.ofFn fun i : Fin n => u.x ⟨i.val % 32, Nat.mod_lt _ (by decide)⟩, u,
      ⟨List.length_ofFn, fun i hi => ?_, fun t ht => by simpa using hf t ht⟩,
      by rw [List.length_ofFn, hp], by rw [List.length_ofFn]; exact h8, r4'.trans ru,
      by rw [pu, after_after, hl, show 15 + 81 * n = 8 + (7 + 81 * n) by omega],
      fun i hi => ?_, ?_, ?_,
      spu.trans (sp4.trans (sp3.trans (sp2.trans sp1))),
      memu.trans (mem4.trans (mem3.trans (mem2.trans mem1))),
      ou.trans (by rw [io4', ← hio])⟩
    · rw [List.getElem_ofFn]
      exact xu i (Nat.zero_le _) (by simp at hi; omega)
    · rw [List.getElem_ofFn]
    · rw [ku 17 (by decide) (by decide) (by decide) (.inr (by show 0 + n ≤ 17; omega)),
        hk4 17 (by decide) (by decide) (by decide) (by decide)]
    · rw [ku 18 (by decide) (by decide) (by decide) (.inr (by show 0 + n ≤ 18; omega)),
        hk4 18 (by decide) (by decide) (by decide) (by decide)]
  · obtain ⟨t, ht, hpre, hft⟩ := exists_first_flagged P.rx (8 * 0) (8 * n) hf
    obtain ⟨u, ru, pu, ou⟩ := hw.2 t ht hpre hft
    have ct' : CodeAt code (after A (8 + (7 + 81 * n) + 1 + 4 + outSize o + 7))
        (movImm 0 (UInt64.ofNat 65) ++ [.b exit]) := by
      rw [show 8 + (7 + 81 * n) + 1 + 4 + outSize o + 7 =
        8 + (movImm 8 P.uart ++ [Instr.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0] ++
          reads).length + 12 + outSize o by rw [hl]; omega]
      exact ct
    obtain ⟨u2, ru2, pu2, xu2, ou2⟩ := run_stub P code ct' hx pu
    refine .inr ⟨u2, r4'.trans (ru.trans ru2), pu2, ⟨xu2, t, ht, by simpa using hft⟩, ?_⟩
    rw [ou2, ou, io4', ← hio]

end LeanExe.A64
