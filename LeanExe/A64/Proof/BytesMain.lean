import LeanExe.A64.Proof.Input
import LeanExe.A64.Proof.ByteMemory

/-!
The parts of the run of `genBytesMain`, the entry routine of a function over bytes.
`gen_bytesMain` gives its code's shape.  `run_readMessage` follows the loop that reads the
message into the block from the allocator: by induction on the bytes that remain, each pass polls
UARTFR, reads UARTDR, and stores the word's low byte with `STRB`, so the machine holds the store
`storeBytes st p (rxBytes P.rx j c)`, the store with the bytes of the reads written from `p`, or
the first byte with an error flag ends the run at the stub of status 65.  `run_writeBytes`
follows the loop that writes the bytes of the returned buffer to the UART, `LDRB` of each byte of
the area and `STRB` to UARTDR, which writes `memBytes st.mem p c`.  A store into the area needs
the UART outside Normal memory, which the program's theorem assumes.
-/

namespace LeanExe.A64

open Wasm

/-- The low bytes of the words of reads `j` to `j + c - 1` of the receiver. -/
def rxBytes (rx : Rx) : Nat → Nat → List UInt8
  | _, 0 => []
  | j, c + 1 => (rx.word j).toUInt8 :: rxBytes rx (j + 1) c

/-- The store `st` with the bytes `bs` written from byte `p` of its memory. -/
def storeBytes (st : Store Unit) (p : Nat) : List UInt8 → Store Unit
  | [] => st
  | b :: bs => storeBytes { st with mem := st.mem.write8 (UInt32.ofNat p) b } (p + 1) bs

/-- The `c` bytes of the memory `m` from byte `p`. -/
def memBytes (m : Mem) : Nat → Nat → List UInt8
  | _, 0 => []
  | p, c + 1 => m.bytes p :: memBytes m (p + 1) c

theorem rxBytes_length (rx : Rx) : ∀ j c, (rxBytes rx j c).length = c
  | _, 0 => rfl
  | j, c + 1 => by rw [rxBytes, List.length_cons, rxBytes_length rx (j + 1) c]

theorem memBytes_length (m : Mem) : ∀ p c, (memBytes m p c).length = c
  | _, 0 => rfl
  | p, c + 1 => by rw [memBytes, List.length_cons, memBytes_length m (p + 1) c]

/-- `storeBytes` keeps the globals and the memory's pages. -/
theorem storeBytes_globals : ∀ (st : Store Unit) (p : Nat) (bs : List UInt8),
    (storeBytes st p bs).globals = st.globals ∧ (storeBytes st p bs).mem.pages = st.mem.pages ∧
      (storeBytes st p bs).memoryCaps = st.memoryCaps
  | _, _, [] => ⟨rfl, rfl, rfl⟩
  | st, p, b :: bs => by
      have := storeBytes_globals { st with mem := st.mem.write8 (UInt32.ofNat p) b } (p + 1) bs
      exact this

/-- The bytes of the memory after `storeBytes`: those of `bs` from `p`, and those of `st`
elsewhere. -/
theorem storeBytes_bytes : ∀ (st : Store Unit) (p : Nat) (bs : List UInt8),
    p + bs.length < 2 ^ 32 → ∀ a, (storeBytes st p bs).mem.bytes a =
      if h : p ≤ a ∧ a < p + bs.length then bs[a - p]'(by omega) else st.mem.bytes a
  | st, p, [], _, a => by simp [storeBytes]
  | st, p, b :: bs, hp, a => by
      rw [storeBytes, storeBytes_bytes _ (p + 1) bs (by simp at hp; omega) a]
      have hp32 : (UInt32.ofNat p).toNat = p := by
        rw [UInt32.toNat_ofNat']
        simp at hp
        omega
      by_cases h1 : p + 1 ≤ a ∧ a < p + 1 + bs.length
      · rw [dif_pos h1, dif_pos (by simp; omega)]
        rw [List.getElem_cons, dif_neg (by omega)]
        congr 1
      · rw [dif_neg h1]
        simp only [Mem.write8, hp32]
        by_cases h2 : a = p
        · subst h2
          simp
        · rw [if_neg h2, dif_neg (by simp; omega)]

/-! ## The code of the entry -/

/-- `genBytesMain`'s code: the frame, the setting of X18 and of the UART's registers, the reads of
the length, the bound, the call of the allocator, the reads of the message, the call of the
function, the writes of its result, the return, and the stubs of statuses 65 and 64. -/
theorem gen_bytesMain {a e a0 inMax uart room base : UInt64} {main : List Instr}
    (hg : genBytesMain a e a0 inMax uart room base = .ok main) :
    ∃ len ov ga msg gk out x65 x64,
      readBytes (after a 146) 7 (after a 16) 0 8 = .ok len ∧
      cbField (after a 101) (after a 151) = .ok ov ∧
      bField (after a 104) a0 = .ok ga ∧
      readMessage (after a 114) (after a 146) = .ok msg ∧
      bField (after a 126) e = .ok gk ∧
      writeBytes (after a 131) = .ok out ∧
      bField (after (after a 146) 4) base = .ok x65 ∧
      bField (after (after a 151) 4) base = .ok x64 ∧
      main = ([.subImm 31 31 16, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
          [.subReg 18 18 16] ++ movImm 8 uart ++
          [.movz 11 0x10 0, .movz 12 0xF00 0, .movz 13 0xFF 0, .movz 7 0 0]) ++
        (len ++ (movImm 16 inMax ++ ([.subsReg 31 7 16, .bcond 8 ov, .str 7 31 1, mov 0 7,
          .bl ga] ++ (movImm 8 uart ++ ([.movz 11 0x10 0, .movz 12 0xF00 0, .addReg 15 17 0,
          .addImm 15 15 1, .ldr 7 31 1] ++ (msg ++ ([.ldr 1 31 1, .bl gk] ++ (movImm 8 uart ++
          (out ++ (movImm 0 0 ++ ([.ldr 30 31 0, .addImm 31 31 16, .ret 30] ++
          ((movImm 0 65 ++ [.b x65]) ++ (movImm 0 64 ++ [.b x64]))))))))))))) := by
  unfold genBytesMain at hg
  cases h1 : readBytes (after a 146) 7 (after a 16) 0 8 with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok len =>
  cases h2 : cbField (after a 101) (after a 151) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok ov =>
  cases h3 : bField (after a 104) a0 with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok ga =>
  cases h4 : readMessage (after a 114) (after a 146) with
  | error err => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok msg =>
  cases h5 : bField (after a 126) e with
  | error err => simp [h1, h2, h3, h4, h5, bind, Except.bind] at hg
  | ok gk =>
  cases h6 : writeBytes (after a 131) with
  | error err => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind] at hg
  | ok out =>
  cases h7 : bField (after (after a 146) 4) base with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, bind, Except.bind] at hg
  | ok x65 =>
  cases h8 : bField (after (after a 151) 4) base with
  | error err => simp [h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind] at hg
  | ok x64 =>
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hg
  refine ⟨len, ov, ga, msg, gk, out, x65, x64, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [← hg]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem readMessage_ok {a err : UInt64} {is : List Instr} (hg : readMessage a err = .ok is) :
    ∃ done back fail loop, cbField a (after a 11) = .ok done ∧
      cbField (after a 3) (after a 1) = .ok back ∧ cbField (after a 6) err = .ok fail ∧
      bField (after a 10) a = .ok loop ∧
      is = [.cbz 7 done, .ldrW 9 8 6, .andReg 10 9 11, .cbnz 10 back, .ldrW 9 8 0,
        .andReg 10 9 12, .cbnz 10 fail, .strb 9 15 4095, .addImm 15 15 1, .subImm 7 7 1,
        .b loop] := by
  unfold readMessage at hg
  cases h1 : cbField a (after a 11) with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok done =>
  cases h2 : cbField (after a 3) (after a 1) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok back =>
  cases h3 : cbField (after a 6) err with
  | error err => simp [h1, h2, h3, bind, Except.bind] at hg
  | ok fail =>
  cases h4 : bField (after a 10) a with
  | error err => simp [h1, h2, h3, h4, bind, Except.bind] at hg
  | ok loop =>
  simp only [h1, h2, h3, h4, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨done, back, fail, loop, rfl, rfl, rfl, rfl, hg.symm⟩

theorem writeBytes_ok {a : UInt64} {is : List Instr} (hg : writeBytes a = .ok is) :
    ∃ done back, cbField (after a 2) (after a 8) = .ok done ∧
      bField (after a 7) (after a 2) = .ok back ∧
      is = [.addReg 3 17 0, .addImm 3 3 1, .cbz 1 done, .ldrb 6 3 4095, .strb 6 8 0,
        .addImm 3 3 1, .subImm 1 1 1, .b back] := by
  unfold writeBytes at hg
  cases h1 : cbField (after a 2) (after a 8) with
  | error err => simp [h1, bind, Except.bind] at hg
  | ok done =>
  cases h2 : bField (after a 7) (after a 2) with
  | error err => simp [h1, h2, bind, Except.bind] at hg
  | ok back =>
  simp only [h1, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hg
  exact ⟨done, back, rfl, rfl, hg.symm⟩

/-! ## Steps -/

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- The code `l1 ++ l2` at `n` instructions after `a`: `l1` there, and `l2` after it. -/
theorem CodeAt.peel {a : UInt64} {l1 l2 : List Instr} {n k : Nat}
    (h : CodeAt code (after a n) (l1 ++ l2)) (hl : l1.length = k) :
    CodeAt code (after a n) l1 ∧ CodeAt code (after a (n + k)) l2 := by
  have := (CodeAt.append (code := code)).mp h
  rw [hl, after_after] at this
  exact this

/-- An instruction that sets register `d`, below 31, to `v` and steps. -/
theorem run_setX {s : State} {i : Instr} {d : Fin 32} {v : UInt64} (hd : d.val < 31)
    (hc : code s.pc = some (encode i))
    (he : LeanExe.A64.exec P i s = some { s.setX d v with pc := s.pc + 4 }) :
    ∃ t, Reach P code s t ∧ t.pc = s.pc + 4 ∧ t.x d = v ∧
      (∀ q : Fin 32, q ≠ d → t.x q = s.x q) ∧ t.sp = s.sp ∧ t.mem = s.mem ∧ t.io = s.io :=
  ⟨_, reach_exec P code hc he (.refl _), rfl,
    by rw [State.x_withPc, State.x_setX_same hd],
    fun q hq => by rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)],
    State.setX_sp, State.setX_mem, State.setX_io⟩

theorem exec_addImm_x {s : State} {d n : Fin 32} {imm : Fin 4096} (hd : d.val < 31)
    (hn : n.val < 31) :
    LeanExe.A64.exec P (.addImm d n imm) s =
      some { s.setX d (s.x n + UInt64.ofNat imm.val) with pc := s.pc + 4 } := by
  simp only [exec, State.xsp_eq_x hn, State.setXsp_eq_setX hd]

theorem exec_subImm_x {s : State} {d n : Fin 32} {imm : Fin 4096} (hd : d.val < 31)
    (hn : n.val < 31) :
    LeanExe.A64.exec P (.subImm d n imm) s =
      some { s.setX d (s.x n - UInt64.ofNat imm.val) with pc := s.pc + 4 } := by
  simp only [exec, State.xsp_eq_x hn, State.setXsp_eq_setX hd]

theorem ofNat_succ_toUInt64 (c : Nat) (hc : c + 1 < 2 ^ 64) :
    UInt64.ofNat (c + 1) - UInt64.ofNat 1 = UInt64.ofNat c := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_sub, UInt64.toNat_ofNat']
  simp only [Nat.reducePow] at *
  omega

theorem ofNat_succ_ne_zero {c : Nat} (hc : c + 1 < 2 ^ 64) : UInt64.ofNat (c + 1) ≠ 0 := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow] at this hc
  omega

theorem toUInt8_toUInt64 (v : UInt32) : v.toUInt64.toUInt8 = v.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt32.toNat_toUInt64, UInt32.toNat_toUInt8]

theorem toUInt8_toUInt64' (v : UInt8) : v.toUInt64.toUInt8 = v := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt8.toNat_toUInt64]
  exact Nat.mod_eq_of_lt v.toNat_lt

theorem addr_4095 (g : UInt64) (p : Nat) :
    g + UInt64.ofNat (p + 1) + UInt64.ofNat (4095 : Fin 4096).val =
      g + UInt64.ofNat (4096 + p) := by
  show g + UInt64.ofNat (p + 1) + UInt64.ofNat 4095 = _
  rw [add_ofNat_add, show p + 1 + 4095 = 4096 + p by omega]

/-- One pass of the loop of `readMessage` at `H`, with `c + 1` bytes to read: when byte `j`
carries no error flag, the run returns to the loop's head with the byte stored at the memory's
byte `p`, X15 one byte further, and X7 one less, and otherwise it reaches `err`. -/
theorem run_msgPass {H err : UInt64} {done back fail : Fin 524288} {loop : Fin 67108864}
    (hc : CodeAt code H [.cbz 7 done, .ldrW 9 8 6, .andReg 10 9 11, .cbnz 10 back, .ldrW 9 8 0,
      .andReg 10 9 12, .cbnz 10 fail, .strb 9 15 4095, .addImm 15 15 1, .subImm 7 7 1, .b loop])
    (hback : cbField (after H 3) (after H 1) = .ok back)
    (hfail : cbField (after H 6) err = .ok fail)
    (hloop : bField (after H 10) H = .ok loop) {cap : Nat} {gts : List ValueType}
    (hU : P.normal P.uart = false) {s : State} {st : Store Unit} {p j c : Nat}
    (hpc : s.pc = H) (h7 : s.x 7 = UInt64.ofNat (c + 1)) (h8 : s.x 8 = P.uart)
    (h11 : s.x 11 = 0x10) (h12 : s.x 12 = 0xF00) (h15 : s.x 15 = s.x 17 + UInt64.ofNat (p + 1))
    (hj : s.io.rxNext = j) (hpo : s.io.rxPolls = 0) (hsr : StoreRel P cap gts st s)
    (hp : p + (c + 1) ≤ st.mem.pages * 65536) :
    (¬ P.rx.Flagged j → ∃ u, Reach P code s u ∧ u.pc = H ∧ u.x 7 = UInt64.ofNat c ∧
        u.x 15 = u.x 17 + UInt64.ofNat (p + 1 + 1) ∧
        (∀ q : Fin 32, q ≠ 7 → q ≠ 9 → q ≠ 10 → q ≠ 15 → u.x q = s.x q) ∧ u.sp = s.sp ∧
        u.mem = store8 s.mem (s.x 17 + UInt64.ofNat (4096 + p)) (P.rx.word j).toUInt8 ∧
        StoreRel P cap gts
          { st with mem := st.mem.write8 (UInt32.ofNat p) (P.rx.word j).toUInt8 } u ∧
        u.io.out = s.io.out ∧ u.io.rxNext = j + 1 ∧ u.io.rxPolls = 0) ∧
    (P.rx.Flagged j → ∃ u, Reach P code s u ∧ u.pc = err ∧ u.io.out = s.io.out) := by
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
  have c10 := hc 10 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3 c4 c5
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c6 c7 c8 c9 c10
  have hpg := hsr.pages
  have hcap := hsr.cap_lt
  have hpp : st.mem.pages * 65536 ≤ 65536 * 65536 := Nat.mul_le_mul_right _ (by omega)
  have hc64 : c + 1 < 2 ^ 64 := by simp only [Nat.reducePow]; omega
  -- the CBZ falls through
  let s1 : State := { s with pc := s.pc + 4 }
  have r1 : Reach P code s s1 :=
    reach_exec P code (by rw [hpc]; exact c0)
      (cbz_next P (by rw [h7]; exact ofNat_succ_ne_zero hc64)) (.refl _)
  have p1 : s1.pc = after H 1 := by show s.pc + 4 = _; rw [hpc, after_succ, after_zero]
  -- the poll loop
  obtain ⟨s2, r2, p2, io2, x2, sp2, mem2⟩ := run_poll P code c1 c2 c3 hback
    (P.rx.wait s1.io.rxNext) s1 p1 h8 h11 (by show s.io.rxPolls + _ = _; rw [hpo]; omega)
  have hj2 : s2.io.rxNext = j := by rw [io2]; exact hj
  have hp2 : s2.io.rxPolls = P.rx.wait j + 1 := by
    rw [io2]
    show P.rx.wait s.io.rxNext + 1 = _
    rw [hj]
  have hout2 : s2.io.out = s.io.out := by rw [io2]
  -- the read of UARTDR
  obtain ⟨hok, hflag⟩ := run_dataRead P code c4 c5 c6 hfail p2
    (by rw [x2 8 (by decide) (by decide)]; exact h8)
    (by rw [x2 12 (by decide) (by decide)]; exact h12) (by rw [hj2, hp2]; omega)
  rw [hj2] at hok hflag
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  rotate_left
  · obtain ⟨u, ru, pu, ou⟩ := hflag hf
    exact ⟨u, r1.trans (r2.trans ru), pu, by rw [ou, hout2]⟩
  obtain ⟨s3, r3, p3, h93, x3, sp3, mem3, io3⟩ := hok hf
  have hx3 : ∀ q : Fin 32, q ≠ 9 → q ≠ 10 → s3.x q = s.x q := fun q h9 h10 => by
    rw [x3 q h9 h10, x2 q h9 h10]
    rfl
  have hmem3 : s3.mem = s.mem := by rw [mem3, mem2]
  have hsr3 : StoreRel P cap gts st s3 :=
    hsr.regs (hx3 17 (by decide) (by decide)) (hx3 18 (by decide) (by decide)) hmem3
  -- the store of the byte
  have hA : s3.x 15 + UInt64.ofNat (4095 : Fin 4096).val =
      s.x 17 + UInt64.ofNat (4096 + p) := by
    rw [hx3 15 (by decide) (by decide), h15, addr_4095]
  have hpcap : p < cap * 65536 := Nat.lt_of_lt_of_le (by omega)
    (Nat.mul_le_mul_right _ hpg.2)
  have hmap : P.normal (s3.x 15 + UInt64.ofNat (4095 : Fin 4096).val) = true := by
    rw [hA, ← hx3 17 (by decide) (by decide)]
    exact hsr3.mapped _ (by unfold areaSize; omega)
  have e4 := exec_strb_base P (s := s3) (t := 9) (n := 15) (imm := 4095) (by decide) hmap hU
  let s4 : State := { s3 with
    mem := store8 s3.mem (s3.x 15 + UInt64.ofNat (4095 : Fin 4096).val) (s3.x 9).toUInt8,
    pc := s3.pc + 4 }
  have hb4 : (s3.x 9).toUInt8 = (P.rx.word j).toUInt8 := by rw [h93, toUInt8_toUInt64]
  have hmem4 : s4.mem =
      store8 s.mem (s.x 17 + UInt64.ofNat (4096 + p)) (P.rx.word j).toUInt8 := by
    show store8 s3.mem _ _ = _
    rw [hmem3, hA, hb4]
  have p4 : s4.pc = after H 8 := by show s3.pc + 4 = _; rw [p3, ← after_succ]
  have hp32 : (UInt32.ofNat p).toNat = p := by
    rw [UInt32.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  have hsr4 : StoreRel P cap gts
      { st with mem := st.mem.write8 (UInt32.ofNat p) (P.rx.word j).toUInt8 } s4 := by
    refine hsr3.write8 P (hy := by rw [hp32]; omega) rfl rfl ?_
    show store8 s3.mem _ _ = _
    rw [hA, hb4, hp32, hx3 17 (by decide) (by decide)]
  -- the steps of X15 and X7 and the branch back
  obtain ⟨s5, r5, p5, x155, k5, sp5, mem5, io5⟩ := run_setX P code (d := 15) (by decide)
    (by rw [p4]; exact c8)
    (exec_addImm_x P (d := 15) (n := 15) (imm := 1) (by decide) (by decide))
  obtain ⟨s6, r6, p6, x76, k6, sp6, mem6, io6⟩ := run_setX P code (d := 7) (by decide)
    (by rw [p5, p4, ← after_succ]; exact c9)
    (exec_subImm_x P (d := 7) (n := 7) (imm := 1) (by decide) (by decide))
  let s7 : State := { s6 with pc := s6.pc + sext 26 loop.val * 4 }
  have e7 : LeanExe.A64.exec P (.b loop) s6 = some s7 := rfl
  have p6' : s6.pc = after H 10 := by rw [p6, p5, p4, ← after_succ, ← after_succ]
  have r7 : Reach P code s6 s7 := reach_exec P code (by rw [p6']; exact c10) e7 (.refl _)
  have hk7 : ∀ q : Fin 32, q ≠ 7 → q ≠ 15 → s7.x q = s4.x q := fun q h7' h15' => by
    show s6.x q = _
    rw [k6 q h7', k5 q h15']
  have hx4 : ∀ q : Fin 32, s4.x q = s3.x q := fun _ => rfl
  refine ⟨s7, r1.trans (r2.trans (r3.trans (reach_exec P code (by rw [p3]; exact c7) e4
      (r5.trans (r6.trans r7))))), ?_, ?_, ?_, fun q hq7 hq9 hq10 hq15 => ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · show s6.pc + sext 26 loop.val * 4 = H
    rw [p6', bField_target hloop]
  · show s6.x 7 = _
    rw [x76, k5 7 (by decide), hx4, hx3 7 (by decide) (by decide), h7]
    exact ofNat_succ_toUInt64 c hc64
  · show s6.x 15 = s6.x 17 + _
    rw [k6 15 (by decide), x155, k6 17 (by decide), k5 17 (by decide), hx4, hx4,
      hx3 15 (by decide) (by decide), hx3 17 (by decide) (by decide), h15, add_ofNat_add]
    rfl
  · rw [hk7 q hq7 hq15, hx4, hx3 q hq9 hq10]
  · show s6.sp = _
    rw [sp6, sp5]
    show s3.sp = _
    rw [sp3, sp2]
  · show s6.mem = _
    rw [mem6, mem5, hmem4]
  · exact hsr4.regs (by show s6.x 17 = _; rw [k6 17 (by decide), k5 17 (by decide)])
      (by show s6.x 18 = _; rw [k6 18 (by decide), k5 18 (by decide)])
      (by show s6.mem = _; rw [mem6, mem5])
  · show s6.io.out = _
    rw [io6, io5]
    show s3.io.out = _
    rw [io3]
    exact hout2
  · show s6.io.rxNext = _
    rw [io6, io5]
    show s3.io.rxNext = _
    rw [io3]
  · show s6.io.rxPolls = _
    rw [io6, io5]
    show s3.io.rxPolls = _
    rw [io3]

/-- The loop of `readMessage` at `H`, from its head with `c` bytes to read, the next read `j` with
no poll done, and X15 at the memory's byte `p` plus 1 less 4096: when no byte among the `c`
carries an error flag, the run leaves the loop with the bytes of the reads written to the memory
from `p`, and otherwise the first flagged byte ends it at `err` with the output kept. -/
theorem run_readMessage {H err : UInt64} {is : List Instr} (hg : readMessage H err = .ok is)
    (hc : CodeAt code H is) {cap : Nat} {gts : List ValueType} (hU : P.normal P.uart = false) :
    ∀ c (s : State) (st : Store Unit) (p j : Nat), s.pc = H → s.x 7 = UInt64.ofNat c →
      s.x 8 = P.uart → s.x 11 = 0x10 → s.x 12 = 0xF00 →
      s.x 15 = s.x 17 + UInt64.ofNat (p + 1) → s.io.rxNext = j → s.io.rxPolls = 0 →
      StoreRel P cap gts st s → p + c ≤ st.mem.pages * 65536 →
      ((∀ t < c, ¬ P.rx.Flagged (j + t)) → ∃ u, Reach P code s u ∧ u.pc = after H 11 ∧
          StoreRel P cap gts (storeBytes st p (rxBytes P.rx j c)) u ∧
          (∀ q : Fin 32, q ≠ 7 → q ≠ 9 → q ≠ 10 → q ≠ 15 → u.x q = s.x q) ∧ u.sp = s.sp ∧
          (∀ a : UInt64, (s.x 18).toNat ≤ a.toNat → u.mem a = s.mem a) ∧
          u.io.out = s.io.out ∧ u.io.rxNext = j + c ∧ u.io.rxPolls = 0) ∧
      (∀ t < c, (∀ i < t, ¬ P.rx.Flagged (j + i)) → P.rx.Flagged (j + t) →
        ∃ u, Reach P code s u ∧ u.pc = err ∧ u.io.out = s.io.out) := by
  obtain ⟨done, back, fail, loop, hdone, hback, hfail, hloop, rfl⟩ := readMessage_ok hg
  have c0 := hc 0 (by simp)
  simp only [List.getElem_cons_zero, after_zero] at c0
  intro c
  induction c with
  | zero =>
    intro s st p j hpc h7 h8 h11 h12 h15 hj hpo hsr hp
    refine ⟨fun _ => ⟨{ s with pc := after H 11 },
      cbz_taken P code (by rw [hpc]; exact c0) hpc hdone (by rw [h7]; rfl), rfl,
      hsr.regs rfl rfl rfl, fun _ _ _ _ _ => rfl, rfl, fun _ _ => rfl, rfl,
      hj.trans (Nat.add_zero j).symm, hpo⟩, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | succ c ih =>
    intro s st p j hpc h7 h8 h11 h12 h15 hj hpo hsr hp
    obtain ⟨hok, hflag⟩ := run_msgPass P code hc hback hfail hloop hU hpc h7 h8 h11 h12 h15 hj
      hpo hsr hp
    have hlim : ∀ a : UInt64, (s.x 18).toNat ≤ a.toNat →
        store8 s.mem (s.x 17 + UInt64.ofNat (4096 + p)) (P.rx.word j).toUInt8 a = s.mem a := by
      intro a ha
      have hpg := hsr.pages
      have hpcap : 4096 + p < areaSize cap := by
        have : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg.2
        unfold areaSize
        omega
      have := hsr.lt_limit hpcap
      exact store8_other _ _ _ _ fun e => by rw [e] at ha; omega
    -- the rest of the loop from the pass's end
    have rest : ¬ P.rx.Flagged j → ∃ u, Reach P code s u ∧ u.pc = H ∧
        u.x 7 = UInt64.ofNat c ∧ u.x 8 = P.uart ∧ u.x 11 = 0x10 ∧ u.x 12 = 0xF00 ∧
        u.x 15 = u.x 17 + UInt64.ofNat (p + 1 + 1) ∧ u.io.rxNext = j + 1 ∧ u.io.rxPolls = 0 ∧
        StoreRel P cap gts
          { st with mem := st.mem.write8 (UInt32.ofNat p) (P.rx.word j).toUInt8 } u ∧
        p + 1 + c ≤
          ({ st with mem := st.mem.write8 (UInt32.ofNat p) (P.rx.word j).toUInt8 } :
            Store Unit).mem.pages * 65536 ∧
        (∀ q : Fin 32, q ≠ 7 → q ≠ 9 → q ≠ 10 → q ≠ 15 → u.x q = s.x q) ∧ u.sp = s.sp ∧
        (∀ a : UInt64, (s.x 18).toNat ≤ a.toNat → u.mem a = s.mem a) ∧
        u.io.out = s.io.out := by
      intro hf
      obtain ⟨u, ru, pu, x7u, x15u, ku, spu, memu, hsru, ou, nu, pou⟩ := hok hf
      exact ⟨u, ru, pu, x7u, by rw [ku 8 (by decide) (by decide) (by decide) (by decide), h8],
        by rw [ku 11 (by decide) (by decide) (by decide) (by decide), h11],
        by rw [ku 12 (by decide) (by decide) (by decide) (by decide), h12], x15u, nu, pou, hsru,
        by show p + 1 + c ≤ (st.mem.write8 _ _).pages * 65536; simp only [Mem.write8]; omega,
        ku, spu, fun a ha => by rw [memu]; exact hlim a ha, ou⟩
    refine ⟨fun hf => ?_, fun t ht hpre hft => ?_⟩
    · obtain ⟨u, ru, pu, x7u, x8u, x11u, x12u, x15u, nu, pou, hsru, hpu, ku, spu, memu, ou⟩ :=
        rest (by simpa using hf 0 (by omega))
      obtain ⟨v, rv, pv, hsrv, kv, spv, memv, ov, nv, pov⟩ :=
        (ih u _ (p + 1) (j + 1) pu x7u x8u x11u x12u x15u nu pou hsru hpu).1 fun t ht => by
          have := hf (t + 1) (by omega)
          rwa [show j + (t + 1) = j + 1 + t by omega] at this
      have hx18 : u.x 18 = s.x 18 := ku 18 (by decide) (by decide) (by decide) (by decide)
      refine ⟨v, ru.trans rv, pv, hsrv, fun q h7' h9 h10 h15' => (kv q h7' h9 h10 h15').trans
        (ku q h7' h9 h10 h15'), spv.trans spu, fun a ha => ?_, ov.trans ou,
        by rw [nv]; omega, pov⟩
      rw [memv a (by rw [hx18]; exact ha), memu a ha]
    · rcases Nat.eq_zero_or_pos t with rfl | htpos
      · exact hflag (by simpa using hft)
      · obtain ⟨u, ru, pu, x7u, x8u, x11u, x12u, x15u, nu, pou, hsru, hpu, ku, spu, memu, ou⟩ :=
          rest (by simpa using hpre 0 htpos)
        obtain ⟨v, rv, pv, ov⟩ := (ih u _ (p + 1) (j + 1) pu x7u x8u x11u x12u x15u nu pou hsru
          hpu).2 (t - 1) (by omega) (fun i hi => by
            have := hpre (i + 1) (by omega)
            rwa [show j + (i + 1) = j + 1 + i by omega] at this)
          (by rwa [show j + 1 + (t - 1) = j + t by omega])
        exact ⟨v, ru.trans rv, pv, ov.trans ou⟩

/-! ## The writes of the result -/

/-- `STRB` with a base other than SP at the UART's data register appends the byte to the
output. -/
theorem exec_strb_uart {s : State} {t n : Fin 32} (hn : n.val < 31)
    (ha : s.x n + UInt64.ofNat (0 : Fin 4096).val = P.uart) :
    LeanExe.A64.exec P (.strb t n 0) s =
      some { s with io := { s.io with out := s.io.out ++ [(s.x t).toUInt8] }, pc := s.pc + 4 } := by
  have h31 : (n.val != 31) = true := by simp; omega
  simp only [exec, State.xsp_eq_x hn, State.spAligned, h31, Bool.true_or, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, ha]

/-- The loop of `writeBytes` at `a`, from its head with `c` bytes to write and X3 at the memory's
byte `p` plus 1 less 4096: the run leaves the loop with the `c` bytes of the memory from `p`
written to the UART. -/
theorem run_writeLoop {a : UInt64} {done : Fin 524288} {back : Fin 67108864}
    (hc : CodeAt code (after a 2) [.cbz 1 done, .ldrb 6 3 4095, .strb 6 8 0, .addImm 3 3 1,
      .subImm 1 1 1, .b back])
    (hdone : cbField (after a 2) (after a 8) = .ok done)
    (hback : bField (after a 7) (after a 2) = .ok back)
    {cap : Nat} {gts : List ValueType} {st : Store Unit} :
    ∀ c (s : State) (p : Nat), s.pc = after a 2 → s.x 1 = UInt64.ofNat c → s.x 8 = P.uart →
      s.x 3 = s.x 17 + UInt64.ofNat (p + 1) → StoreRel P cap gts st s →
      p + c ≤ st.mem.pages * 65536 →
      ∃ u, Reach P code s u ∧ u.pc = after a 8 ∧
        u.io.out = s.io.out ++ memBytes st.mem p c ∧ u.sp = s.sp ∧ u.mem = s.mem ∧
        u.io.rxNext = s.io.rxNext ∧ u.io.rxPolls = s.io.rxPolls ∧
        (∀ q : Fin 32, q ≠ 1 → q ≠ 3 → q ≠ 6 → u.x q = s.x q) := by
  have c0 := hc 0 (by simp)
  have c1 := hc 1 (by simp)
  have c2 := hc 2 (by simp)
  have c3 := hc 3 (by simp)
  have c4 := hc 4 (by simp)
  have c5 := hc 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c0 c1 c2
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero, after_after] at c3 c4 c5
  intro c
  induction c with
  | zero =>
    intro s p hpc h1 h8 h3 hsr hp
    exact ⟨{ s with pc := after a 8 }, cbz_taken P code (by rw [hpc]; exact c0) hpc hdone
      (by rw [h1]; rfl), rfl, by simp [memBytes], rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | succ c ih =>
    intro s p hpc h1 h8 h3 hsr hp
    have hpg := hsr.pages
    have hcap := hsr.cap_lt
    have hpp : st.mem.pages * 65536 ≤ 65536 * 65536 := Nat.mul_le_mul_right _ (by omega)
    have hc64 : c + 1 < 2 ^ 64 := by simp only [Nat.reducePow]; omega
    let s1 : State := { s with pc := s.pc + 4 }
    have r1 : Reach P code s s1 :=
      reach_exec P code (by rw [hpc]; exact c0)
        (cbz_next P (by rw [h1]; exact ofNat_succ_ne_zero hc64)) (.refl _)
    have p1 : s1.pc = after a 3 := by show s.pc + 4 = _; rw [hpc, ← after_succ]
    -- the byte from the area
    have hA : s1.x 3 + UInt64.ofNat (4095 : Fin 4096).val = s.x 17 + UInt64.ofNat (4096 + p) := by
      show s.x 3 + _ = _
      rw [h3, addr_4095]
    have hpcap : 4096 + p < areaSize cap := by
      have : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg.2
      unfold areaSize
      omega
    obtain ⟨s2, r2, p2, x62, k2, sp2, mem2, io2⟩ := run_setX P code (d := 6) (by decide)
      (by rw [p1]; exact c1) (exec_ldrb_base P (s := s1) (t := 6) (n := 3) (imm := 4095)
        (by decide) (by rw [hA]; exact hsr.mapped _ hpcap))
    have hv2 : (s2.x 6).toUInt8 = st.mem.bytes p := by
      rw [x62, hA]
      show (s.mem (s.x 17 + UInt64.ofNat (4096 + p))).toUInt64.toUInt8 = _
      rw [hsr.bytes p (by
        have : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg.2
        omega), toUInt8_toUInt64']
    -- the byte to the UART
    have h82 : s2.x 8 + UInt64.ofNat (0 : Fin 4096).val = P.uart := by
      rw [k2 8 (by decide)]
      show s.x 8 + 0 = _
      rw [UInt64.add_zero, h8]
    let s3 : State :=
      { s2 with io := { s2.io with out := s2.io.out ++ [(s2.x 6).toUInt8] }, pc := s2.pc + 4 }
    have e3 := exec_strb_uart P (s := s2) (t := 6) (n := 8) (by decide) h82
    have p2' : s2.pc = after a 4 := by rw [p2, p1, ← after_succ]
    have p3 : s3.pc = after a 5 := by show s2.pc + 4 = _; rw [p2', ← after_succ]
    obtain ⟨s4, r4, p4, x34, k4, sp4, mem4, io4⟩ := run_setX P code (d := 3) (by decide)
      (by rw [p3]; exact c3)
      (exec_addImm_x P (s := s3) (d := 3) (n := 3) (imm := 1) (by decide) (by decide))
    obtain ⟨s5, r5, p5, x15, k5, sp5, mem5, io5⟩ := run_setX P code (d := 1) (by decide)
      (by rw [p4, p3, ← after_succ]; exact c4)
      (exec_subImm_x P (s := s4) (d := 1) (n := 1) (imm := 1) (by decide) (by decide))
    let s6 : State := { s5 with pc := s5.pc + sext 26 back.val * 4 }
    have e6 : LeanExe.A64.exec P (.b back) s5 = some s6 := rfl
    have p5' : s5.pc = after a 7 := by rw [p5, p4, p3, ← after_succ, ← after_succ]
    have r6 : Reach P code s5 s6 := reach_exec P code (by rw [p5']; exact c5) e6 (.refl _)
    have hk6 : ∀ q : Fin 32, q ≠ 1 → q ≠ 3 → q ≠ 6 → s6.x q = s.x q := fun q h1' h3' h6' => by
      show s5.x q = _
      rw [k5 q h1', k4 q h3']
      show s2.x q = _
      rw [k2 q h6']
      rfl
    have hsr6 : StoreRel P cap gts st s6 := hsr.regs (hk6 17 (by decide) (by decide) (by decide))
      (hk6 18 (by decide) (by decide) (by decide))
      (by show s5.mem = _; rw [mem5, mem4]; show s2.mem = _; rw [mem2])
    obtain ⟨u, ru, pu, ou, spu, memu, nu, pou, ku⟩ := ih s6 (p + 1)
      (by show s5.pc + sext 26 back.val * 4 = _; rw [p5', bField_target hback])
      (by
        show s5.x 1 = _
        rw [x15, k4 1 (by decide)]
        show s2.x 1 - _ = _
        rw [k2 1 (by decide)]
        show s.x 1 - _ = _
        rw [h1]
        exact ofNat_succ_toUInt64 c hc64)
      (by rw [hk6 8 (by decide) (by decide) (by decide), h8])
      (by
        show s5.x 3 = s5.x 17 + _
        rw [k5 3 (by decide), x34, k5 17 (by decide), k4 17 (by decide)]
        show s2.x 3 + _ = s2.x 17 + _
        rw [k2 3 (by decide), k2 17 (by decide)]
        show s.x 3 + _ = s.x 17 + _
        rw [h3, add_ofNat_add]
        rfl)
      hsr6 (by omega)
    have hio : s6.io = { s.io with out := s.io.out ++ [st.mem.bytes p] } := by
      show s5.io = _
      rw [io5, io4]
      show { s2.io with out := s2.io.out ++ [(s2.x 6).toUInt8] } = _
      rw [hv2, io2]
      try rfl
    refine ⟨u, r1.trans (r2.trans (reach_exec P code (by rw [p2']; exact c2) e3
      (r4.trans (r5.trans (r6.trans ru))))), pu, ?_, spu.trans (sp5.trans (sp4.trans sp2)),
      memu.trans (mem5.trans (mem4.trans mem2)), by rw [nu, hio], by rw [pou, hio],
      fun q h1' h3' h6' => by rw [ku q h1' h3' h6', hk6 q h1' h3' h6']⟩
    rw [ou, hio, List.append_assoc]
    rfl

