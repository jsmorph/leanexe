import LeanExe.A64.Proof.Memory

/-!
The simulation of `i32.load8_u` and `i32.store8`.  Each compares the address with the memory's
size less 8, plus 7 less the offset `off`, branches to the stub of an access outside the memory
above it, and accesses the byte `X17 + 4096 + a + off` with `LDRB` or `STRB` 4095 bytes above
`X17 + a + off + 1`.  The area is Normal memory, so `LDRB` reads it.  `STRB` writes to the UART
when its address is the UART's, so the store's lemma takes from `CallsOk` that a program whose
functions store bytes has its UART outside Normal memory, and every byte of the area is Normal
memory.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

theorem add_ofNat_sub_seven {x : UInt64} {off : Nat} (h : off ≤ 7) :
    x + UInt64.ofNat (7 - off) = x + 7 - UInt64.ofNat off := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.reduceToNat,
    Nat.reducePow] at *
  omega

theorem sub_ofNat_sub_seven {x : UInt64} {off : Nat} (h : 7 < off) (h' : off < 4095) :
    x - UInt64.ofNat (off - 7) = x + 7 - UInt64.ofNat off := by
  apply UInt64.toNat_inj.mp
  have := x.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.reduceToNat,
    Nat.reducePow] at *
  omega

/-- `boundInstr off` adds 7 less `off` to X16. -/
theorem exec_boundInstr {off : Nat} (h : off < 4095) (s : State) :
    exec P (boundInstr off h) s =
      some { s.setX 16 (s.x 16 + 7 - UInt64.ofNat off) with pc := s.pc + 4 } := by
  have h16 : (16 : Fin 32).val < 31 := by decide
  unfold boundInstr
  split
  · rename_i h7
    simp only [exec, State.xsp_eq_x h16, State.setXsp_eq_setX h16]
    rw [add_ofNat_sub_seven h7]
  · rename_i h7
    simp only [exec, State.xsp_eq_x h16, State.setXsp_eq_setX h16]
    rw [sub_ofNat_sub_seven (by omega) h]

/-- The bounds check of a 1-byte access at offset `off` on the address in `r`: the run reaches the
access's fifth instruction when the byte lies within the memory, and the stub `tB` otherwise,
changing X16 and the flags alone. -/
theorem run_bounds8 {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α} {ms : State}
    {a tB : UInt64} {r : Fin 32} {off : Nat} (hoff : off < 4095) {g : Fin 524288}
    (hr : r.val < 31) (hr16 : r ≠ 16)
    (hcode : CodeAt code a [.ldr 16 17 0, boundInstr off hoff, .subsReg 31 r 16, .bcond 8 g])
    (hg : cbField (after a 3) tB = .ok g) (hpc : ms.pc = a)
    (hsr : StoreRel P cap gts st ms) :
    ∃ s, Reach P code ms s ∧ s.sp = ms.sp ∧ s.mem = ms.mem ∧ s.io = ms.io ∧
      (∀ q, q ≠ 16 → s.x q = ms.x q) ∧
      s.pc = if (ms.x r).toNat + off + 1 ≤ st.mem.pages * 65536 then after a 4 else tB := by
  have c0 := hcode 0 (by simp)
  have c1 := hcode 1 (by simp)
  have c2 := hcode 2 (by simp)
  have c3 := hcode 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  have hex := exec_ldr_base P (s := ms) (t := 16) (i := 0) (by decide) (n := 17) (by decide)
    (fun k hk => hsr.mapped _ (by unfold areaSize; omega))
  simp only [Nat.mul_zero, add_ofNat_zero] at hex
  let S := load64 ms.mem (ms.x 17)
  let s1 : State := { ms.setX 16 S with pc := ms.pc + 4 }
  let s2 : State := { s1.setX 16 (s1.x 16 + 7 - UInt64.ofNat off) with pc := s1.pc + 4 }
  let s3 : State := { s2.subs 31 (s2.x r) (s2.x 16) with pc := s2.pc + 4 }
  let s4 : State :=
    { s3 with pc := if s3.condHolds 8 then s3.pc + sext 19 g.val * 4 else s3.pc + 4 }
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by
    show s1.pc + 4 = _
    rw [p1, ← after_succ]
  have p3 : s3.pc = after a 3 := by
    show s2.pc + 4 = _
    rw [p2, ← after_succ]
  have e1 : LeanExe.A64.exec P (boundInstr off hoff) s1 = some s2 := exec_boundInstr P hoff s1
  have e2 : LeanExe.A64.exec P (.subsReg 31 r 16) s2 = some s3 := rfl
  have e3 : LeanExe.A64.exec P (.bcond 8 g) s3 = some s4 := rfl
  have hreach : Reach P code ms s4 :=
    reach_exec P code (by rw [hpc]; exact c0) hex
      (reach_exec P code (by rw [p1]; exact c1) e1
        (reach_exec P code (by rw [p2]; exact c2) e2
          (reach_exec P code (by rw [p3]; exact c3) e3 (.refl _))))
  have hx1 : ∀ q, q ≠ 16 → s1.x q = ms.x q := fun q hq => by
    show (ms.setX 16 S).x q = _
    exact State.x_setX_ne (Ne.symm hq)
  have hx2 : ∀ q, q ≠ 16 → s2.x q = ms.x q := fun q hq => by
    show (s1.setX 16 _).x q = _
    rw [State.x_setX_ne (Ne.symm hq), hx1 q hq]
  have hx3 : ∀ q, s3.x q = s2.x q := fun q => by
    show (s2.setX 31 (s2.x r - s2.x 16)).x q = _
    unfold State.setX
    rw [ite_eq_right (by decide)]
  have h16 : s2.x 16 = UInt64.ofNat (st.mem.pages * 65536 - 1 - off) := by
    show (s1.setX 16 (s1.x 16 + 7 - UInt64.ofNat off)).x 16 = _
    rw [State.x_setX_same (by decide)]
    have hs1 : s1.x 16 = S := by
      show (ms.setX 16 S).x 16 = _
      exact State.x_setX_same (by decide)
    rw [hs1]
    show load64 ms.mem (ms.x 17) + 7 - _ = _
    rw [hsr.size]
    have := hsr.pages
    have := hsr.cap_lt
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      UInt64.toNat_ofNat']
    simp only [Nat.reducePow, UInt64.reduceToNat] at *
    omega
  have hxr : s2.x r = ms.x r := hx2 r hr16
  have hcond : s3.condHolds 8 = !decide ((ms.x r).toNat + off + 1 ≤ st.mem.pages * 65536) := by
    rw [condHolds_8]
    show (decide (s2.x 16 ≤ s2.x r) && !(s2.x r - s2.x 16 == 0)) = _
    rw [hxr, h16]
    have := hsr.pages
    have := hsr.cap_lt
    have hlt := (ms.x r).toNat_lt
    by_cases hc : (ms.x r).toNat + off + 1 ≤ st.mem.pages * 65536
    · have h1 : ¬ (UInt64.ofNat (st.mem.pages * 65536 - 1 - off) ≤ ms.x r ∧
          ms.x r ≠ UInt64.ofNat (st.mem.pages * 65536 - 1 - off)) := by
        rw [UInt64.le_iff_toNat_le, Ne, ← UInt64.toNat_inj, UInt64.toNat_ofNat']
        simp only [Nat.reducePow] at *
        omega
      rw [decide_eq_true hc]
      by_cases h2 : UInt64.ofNat (st.mem.pages * 65536 - 1 - off) ≤ ms.x r
      · have h3 : ms.x r = UInt64.ofNat (st.mem.pages * 65536 - 1 - off) := by
          exact Classical.byContradiction fun hne => h1 ⟨h2, hne⟩
        rw [h3]
        simp
      · simp [h2]
    · have h1 : UInt64.ofNat (st.mem.pages * 65536 - 1 - off) < ms.x r := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
        simp only [Nat.reducePow] at *
        omega
      rw [decide_eq_false hc]
      have h2 : ms.x r - UInt64.ofNat (st.mem.pages * 65536 - 1 - off) ≠ 0 := fun e =>
        absurd ((sub_eq_zero_iff' _ _).mp e) (fun e' => by
          rw [e', UInt64.lt_iff_toNat_lt] at h1
          omega)
      simp [UInt64.le_of_lt h1, h2]
  refine ⟨s4, hreach, ?_, ?_, ?_, fun q hq => ?_, ?_⟩
  · show (s2.setX 31 (s2.x r - s2.x 16)).sp = _
    rw [State.setX_sp]
    show (s1.setX 16 (s1.x 16 + 7 - UInt64.ofNat off)).sp = _
    rw [State.setX_sp]
    show (ms.setX 16 S).sp = _
    exact State.setX_sp
  · show (s2.setX 31 (s2.x r - s2.x 16)).mem = _
    rw [State.setX_mem]
    show (s1.setX 16 (s1.x 16 + 7 - UInt64.ofNat off)).mem = _
    rw [State.setX_mem]
    show (ms.setX 16 S).mem = _
    exact State.setX_mem
  · show (s2.setX 31 (s2.x r - s2.x 16)).io = _
    rw [State.setX_io]
    show (s1.setX 16 (s1.x 16 + 7 - UInt64.ofNat off)).io = _
    rw [State.setX_io]
    show (ms.setX 16 S).io = _
    exact State.setX_io
  · show s3.x q = _
    rw [hx3, hx2 q hq]
  · show (if s3.condHolds 8 then s3.pc + sext 19 g.val * 4 else s3.pc + 4) = _
    rw [hcond, p3]
    by_cases hc : (ms.x r).toNat + off + 1 ≤ st.mem.pages * 65536
    · rw [ite_eq_left hc]
      simp only [decide_eq_true hc, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (after_succ a 3).symm
    · rw [ite_eq_right hc]
      simp only [decide_eq_false hc, Bool.not_false, ite_true]
      exact cbField_target hg

/-- The address `X17 + a + (off + 1) + 4095` of a 1-byte access is the memory's byte `a + off`. -/
theorem byte_addr {g w : UInt64} {off : Nat} (hoff : off < 4095) :
    g + w + UInt64.ofNat (off + 1) + UInt64.ofNat 4095 =
      g + UInt64.ofNat (4096 + (w.toNat + off)) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat']
  have := w.toNat_lt
  simp only [Nat.reducePow] at *
  omega

/-- The first four instructions of a 1-byte access: its bounds check. -/
theorem CodeAt.take4' {a : UInt64} {i0 i1 i2 i3 i4 i5 i6 : Instr}
    (h : CodeAt code a [i0, i1, i2, i3, i4, i5, i6]) : CodeAt code a [i0, i1, i2, i3] := by
  intro i hi
  have := h i (by simp at hi ⊢; omega)
  simp at hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> exact this

/-! ## `i32.load8_u` -/

theorem gen_load8U {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.load8U off) = .ok (is, fin)) :
    ∃ (h : off.toNat < 4095) (g : Fin 524288), curBase ctl + 1 ≤ σ.length ∧
      (σ.head? = some .i32 ∨ σ.head? = some .i64) ∧ σ.length - 1 < 26 ∧
      cbField (after a 3) E.trapBounds = .ok g ∧
      is = [.ldr 16 17 0, boundInstr off.toNat h, .subsReg 31 (regOf (σ.length - 1)) 16,
        .bcond 8 g, .addReg 16 17 (regOf (σ.length - 1)), .addImm 16 16 ⟨off.toNat + 1, by omega⟩,
        .ldrb (regOf (σ.length - 1)) 16 4095] ∧
      fin = some (.i32 :: σ.tail) := by
  unfold genInstr at hg
  by_cases hc : σ.length < curBase ctl + 1 ∨ ¬ (σ.head? = some .i32 ∨ σ.head? = some .i64)
  · simp only [hc, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc, ite_false] at hg
  have hc' := hc
  simp only [not_or, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2⟩ := hc'
  by_cases h : off.toNat < 4095
  · by_cases hlt : σ.length - 1 < 26
    · cases hcb : cbField (after a 3) E.trapBounds with
      | error e => simp [h, opReg_ok hlt, hcb, bind, Except.bind] at hg
      | ok g =>
          simp [h, opReg_ok hlt, hcb, bind, Except.bind, pure, Except.pure] at hg
          exact ⟨h, g, by omega, Classical.byContradiction fun hn =>
            hc2 ⟨fun h => hn (.inl h), fun h => hn (.inr h)⟩, hlt, rfl,
            hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [h, he, bind, Except.bind] at hg
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

/-- `LDRB` with a base other than SP of a byte of Normal memory. -/
theorem exec_ldrb_base {s : State} {t n : Fin 32} {imm : Fin 4096} (hn : n.val < 31)
    (hmap : P.normal (s.x n + UInt64.ofNat imm.val) = true) :
    LeanExe.A64.exec P (.ldrb t n imm) s =
      some { s.setX t (s.mem (s.x n + UInt64.ofNat imm.val)).toUInt64 with pc := s.pc + 4 } := by
  have h31 : (n.val != 31) = true := by simp; omega
  simp only [exec, State.xsp_eq_x hn, State.spAligned, h31, Bool.true_or, hmap, Bool.and_self,
    ↓reduceIte]

/-- `STRB` with a base other than SP of a byte of Normal memory, on a platform whose UART lies
outside Normal memory. -/
theorem exec_strb_base {s : State} {t n : Fin 32} {imm : Fin 4096} (hn : n.val < 31)
    (hmap : P.normal (s.x n + UInt64.ofNat imm.val) = true)
    (hU : P.normal P.uart = false) :
    LeanExe.A64.exec P (.strb t n imm) s =
      some { s with
        mem := store8 s.mem (s.x n + UInt64.ofNat imm.val) (s.x t).toUInt8, pc := s.pc + 4 } := by
  have h31 : (n.val != 31) = true := by simp; omega
  have hne : ¬ s.x n + UInt64.ofNat imm.val = P.uart := fun e => by
    rw [e, hU] at hmap
    cases hmap
  simp only [exec, State.xsp_eq_x hn, State.spAligned, h31, Bool.true_or, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hne, hmap]

theorem sim_load8U (F : Nat) (off : UInt32) : InstrSim P code F (.load8U off) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ D _ _
  obtain ⟨h, g, hc1, hty0, hlt, hg, rfl, rfl⟩ := gen_load8U hgen
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      obtain ⟨t, σ0, rfl⟩ : ∃ t σ0, σ = t :: σ0 := by
        cases σ with
        | nil => simp at hc1
        | cons t σ0 => exact ⟨t, σ0, rfl⟩
      simp only [List.length_cons, Nat.add_sub_cancel, List.tail_cons] at hlt hcode hc1 ⊢
      simp only [List.head?_cons, Option.some.injEq] at hty0
      obtain ⟨v, vs, hvs⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hv : sl.values with
        | nil => rw [hv] at hh; simp at hh
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hstack := hinv.stack
      rw [hvs] at hstack
      have hty := hinv.types
      rw [hvs] at hty
      have hvl : vs.length = σ0.length := by rw [hvs] at hh; simpa using hh
      have htop : ValRel v (ms.x (regOf σ0.length)) := by
        have := hstack.top
        rwa [hvl] at this
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      generalize hn : (ms.x (regOf σ0.length)).toNat = n
      suffices key : ∀ y : UInt32, (n + off.toNat + 1 ≤ st.mem.pages * 65536 →
          y.toNat = n + off.toNat) →
          Outcome P code E ctl D (some (.i32 :: σ0)) (after a 7)
            (if n + off.toNat + 1 > st.mem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else .Fallthrough st { sl with values := .i32 (st.mem.read8 y).toUInt32 :: vs }) ms by
        rcases addr_cases hty.1 hty0 with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · have hx : n = x.toNat := by rw [← hn, htop]; simp
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x + off) fun hin => ?_
          rw [UInt32.toNat_add, ← hx]
          simp only [Nat.reducePow] at *
          omega
        · have hx : n = x.toNat := by rw [← hn, htop]
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x.toUInt32 + off) fun hin => ?_
          rw [UInt32.toNat_add, UInt64.toNat_toUInt32, ← hx]
          simp only [Nat.reducePow] at *
          omega
      intro y hy
      have hr := regOf_lt_31 _ hlt
      have hr16 : regOf σ0.length ≠ 16 := regOf_ne_scratch _ hlt
      obtain ⟨s, hrs, hsps, hmems, houts, hxs, hpcs⟩ :=
        run_bounds8 P code (r := regOf σ0.length) h hr hr16 (CodeAt.take4' code hcode) hg hpc
          hsr
      rw [hn] at hpcs
      by_cases hin : n + off.toNat + 1 ≤ st.mem.pages * 65536
      · rw [ite_eq_right (by omega)]
        rw [ite_eq_left hin] at hpcs
        have c4 := hcode 4 (by simp)
        have c5 := hcode 5 (by simp)
        have c6 := hcode 6 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c4 c5 c6
        let s5 : State := { s.setX 16 (s.x 17 + s.x (regOf σ0.length)) with pc := s.pc + 4 }
        have e5 : LeanExe.A64.exec P (.addReg 16 17 (regOf σ0.length)) s = some s5 := rfl
        have p5 : s5.pc = after a 5 := by
          show s.pc + 4 = _
          rw [hpcs, ← after_succ]
        have h16 : s5.x 16 = ms.x 17 + ms.x (regOf σ0.length) := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x 16 = _
          rw [State.x_setX_same (by decide), hxs 17 (by decide), hxs _ hr16]
        let s6 : State :=
          { s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1)) with pc := s5.pc + 4 }
        have e6 : LeanExe.A64.exec P (.addImm 16 16 ⟨off.toNat + 1, by omega⟩) s5 = some s6 := by
          simp only [exec, State.xsp_eq_x (show (16 : Fin 32).val < 31 by decide),
            State.setXsp_eq_setX (show (16 : Fin 32).val < 31 by decide)]
          rfl
        have p6 : s6.pc = after a 6 := by
          show s5.pc + 4 = _
          rw [p5, ← after_succ]
        have h16' : s6.x 16 = ms.x 17 + ms.x (regOf σ0.length) + UInt64.ofNat (off.toNat + 1) := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).x 16 = _
          rw [State.x_setX_same (by decide), h16]
        have hbound : n + off.toNat + 1 ≤ E.cap * 65536 :=
          Nat.le_trans hin (Nat.mul_le_mul_right _ hpg.2)
        have hb : s6.x 16 + UInt64.ofNat (4095 : Fin 4096).val =
            ms.x 17 + UInt64.ofNat (4096 + (n + off.toNat)) := by
          show s6.x 16 + UInt64.ofNat 4095 = _
          rw [h16', byte_addr (by omega), hn]
        have hex7 := exec_ldrb_base P (s := s6) (t := regOf σ0.length) (imm := 4095) (n := 16)
          (by decide) (by
            rw [hb]
            exact hsr.mapped _ (by unfold areaSize; omega))
        have hmem6 : s6.mem = ms.mem := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).mem = _
          rw [State.setX_mem]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).mem = _
          rw [State.setX_mem, hmems]
        have hval : (s6.mem (s6.x 16 + UInt64.ofNat (4095 : Fin 4096).val)).toUInt64 =
            (st.mem.read8 y).toUInt32.toUInt64 := by
          rw [hmem6, hb, hsr.bytes _ (by omega), Mem.read8, hy hin]
          rfl
        let s7 : State := { s6.setX (regOf σ0.length)
          (s6.mem (s6.x 16 + UInt64.ofNat (4095 : Fin 4096).val)).toUInt64 with pc := s6.pc + 4 }
        have hr7 : Reach P code ms s7 :=
          hrs.trans (reach_exec P code (by rw [hpcs]; exact c4) e5
            (reach_exec P code (by rw [p5]; exact c5) e6
              (reach_exec P code (by rw [p6]; exact c6) hex7 (.refl _))))
        have hk7 : ∀ q, q ≠ regOf σ0.length → q ≠ 16 → s7.x q = ms.x q := fun q hq hq16 => by
          show (s6.setX (regOf σ0.length) _).x q = _
          rw [State.x_setX_ne (Ne.symm hq)]
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).x q = _
          rw [State.x_setX_ne (Ne.symm hq16)]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x q = _
          rw [State.x_setX_ne (Ne.symm hq16), hxs q hq16]
        have hsp6 : s6.sp = ms.sp := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).sp = _
          rw [State.setX_sp]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).sp = _
          rw [State.setX_sp, hsps]
        have hio6 : s6.io = ms.io := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).io = _
          rw [State.setX_io]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).io = _
          rw [State.setX_io, houts]
        refine res_outcome P code (v := .i32 (st.mem.read8 y).toUInt32) (t := .i32) (vs := vs)
          (w := s7.x (regOf σ0.length)) ?_
          (show HasType .i32 (.i32 (st.mem.read8 y).toUInt32) from ⟨⟩)
          hty.2 hinv hsr (by omega) (by omega)
          hstack.pop hr7 ?_ (by rw [hvl]) ?_ (hk7 18 (Ne.symm (regOf_ne_18 _ hlt)) (by decide))
          (hk7 17 (Ne.symm (regOf_ne_17 _ hlt)) (by decide)) ?_ ?_ ?_
        · show (s6.setX (regOf σ0.length) _).x (regOf σ0.length) = _
          rw [State.x_setX_same hr, hval]
        · show s6.pc + 4 = after a 7
          rw [p6, ← after_succ]
        · intro k hk
          exact hk7 _ (fun e => absurd (regOf_inj k (by omega) _ hlt e) (by omega))
            (regOf_ne_scratch k (by omega))
        · show (s6.setX (regOf σ0.length) _).sp = _
          rw [State.setX_sp, hsp6]
        · show (s6.setX (regOf σ0.length) _).mem = _
          rw [State.setX_mem, hmem6]
        · show (s6.setX (regOf σ0.length) _).io = _
          rw [State.setX_io, hio6]
      · rw [ite_eq_left (by omega)]
        rw [ite_eq_right hin] at hpcs
        exact .inr ⟨s, hrs, houts, .inr (.inl ⟨rfl, hpcs⟩)⟩

/-! ## `i32.store8` -/

theorem gen_store8 {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {off : UInt32}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.store8 off) = .ok (is, fin)) :
    ∃ (h : off.toNat < 4095) (g : Fin 524288), E.byteStores = true ∧
      curBase ctl + 2 ≤ σ.length ∧ σ.head? = some .i32 ∧
      (σ[1]? = some .i32 ∨ σ[1]? = some .i64) ∧ σ.length - 1 < 26 ∧
      cbField (after a 3) E.trapBounds = .ok g ∧
      is = [.ldr 16 17 0, boundInstr off.toNat h, .subsReg 31 (regOf (σ.length - 2)) 16,
        .bcond 8 g, .addReg 16 17 (regOf (σ.length - 2)),
        .addImm 16 16 ⟨off.toNat + 1, by omega⟩, .strb (regOf (σ.length - 1)) 16 4095] ∧
      fin = some (σ.drop 2) := by
  unfold genInstr at hg
  cases hB : E.byteStores with
  | false => simp [hB, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  | true =>
  simp only [hB, Bool.not_true, Bool.false_eq_true, ite_false] at hg
  by_cases hc : σ.length < curBase ctl + 2 ∨ σ.head? ≠ some .i32 ∨
      ¬ (σ[1]? = some .i32 ∨ σ[1]? = some .i64)
  · simp only [hc, ite_true] at hg
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  simp only [hc, ite_false] at hg
  have hc' := hc
  simp only [not_or, Ne, Decidable.not_not] at hc'
  obtain ⟨hc1, hc2, hc3⟩ := hc'
  by_cases h : off.toNat < 4095
  · by_cases hlt : σ.length - 1 < 26
    · have hlt2 : σ.length - 2 < 26 := by omega
      cases hcb : cbField (after a 3) E.trapBounds with
      | error e => simp [h, opReg_ok hlt, opReg_ok hlt2, hcb, bind, Except.bind] at hg
      | ok g =>
          simp [h, opReg_ok hlt, opReg_ok hlt2, hcb, bind, Except.bind, pure, Except.pure] at hg
          exact ⟨h, g, rfl, by omega, hc2, Classical.byContradiction fun hn =>
            hc3 ⟨fun h => hn (.inl h), fun h => hn (.inr h)⟩, hlt, rfl, hg.1.symm, hg.2.symm⟩
    · obtain ⟨e, he⟩ := opReg_error hlt
      simp [h, he, bind, Except.bind] at hg
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg

theorem store8_other (m : UInt64 → UInt8) (a b : UInt64) (v : UInt8) (h : b ≠ a) :
    store8 m a v b = m b := by
  simp [store8, h]

/-- The machine's store of the byte `v` at byte `y` of the memory in the area at `g` leaves byte
`j` of the memory as Talos's `write8` does. -/
theorem write8_byte {mem : UInt64 → UInt8} {g : UInt64} {m : Mem} {y : UInt32} {v : UInt8}
    {j : Nat} (hy : g.toNat + 4096 + y.toNat < 2 ^ 64) (hj : g.toNat + 4096 + j < 2 ^ 64)
    (hmem : mem (g + UInt64.ofNat (4096 + j)) = m.bytes j) :
    store8 mem (g + UInt64.ofNat (4096 + y.toNat)) v (g + UInt64.ofNat (4096 + j)) =
      (m.write8 y v).bytes j := by
  by_cases hin : j = y.toNat
  · subst hin
    simp [store8, Mem.write8]
  · rw [store8_other _ _ _ _ fun e => hin (by
      have := congrArg UInt64.toNat e
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
      simp only [Nat.reducePow] at *
      omega)]
    simp only [Mem.write8, hin, ite_false]
    exact hmem

/-- The store relation after a store of the byte `v` at byte `y` of the memory, within its
size. -/
theorem StoreRel.write8 {cap : Nat} {gts : List ValueType} {α : Type} {st : Store α}
    {s s' : State} (h : StoreRel P cap gts st s) {y : UInt32} {v : UInt8}
    (hy : y.toNat + 1 ≤ st.mem.pages * 65536) (h17 : s'.x 17 = s.x 17) (h18 : s'.x 18 = s.x 18)
    (hmem : s'.mem = store8 s.mem (s.x 17 + UInt64.ofNat (4096 + y.toNat)) v) :
    StoreRel P cap gts { st with mem := st.mem.write8 y v } s' := by
  have hgl := h.glen
  have hlen := h.types.length
  have hbelow := h.below
  have hx18 := (s.x 18).toNat_lt
  have hcap : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ h.pages.2
  unfold areaSize at hbelow
  have hne : ∀ k < 4096, s.x 17 + UInt64.ofNat k ≠ s.x 17 + UInt64.ofNat (4096 + y.toNat) :=
    fun k hk e => by
      have := congrArg UInt64.toNat e
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
      simp only [Nat.reducePow] at *
      omega
  refine ⟨h.caps, h.cap_lt, h.glen, h.pages, ?_, h.types, ?_, ?_, ?_, ?_⟩
  · rw [hmem, h17, load64_congr (m := store8 _ _ _) (m' := s.mem) fun k hk => by
      rw [show s.x 17 + UInt64.ofNat k = s.x 17 + UInt64.ofNat k from rfl]
      exact store8_other _ _ _ _ (hne k (by omega))]
    exact h.size
  · intro i hi
    have hi' : i < st.globals.globals.length := hi
    rw [hmem, h17, load64_congr (m := store8 _ _ _) (m' := s.mem) fun k hk => by
      rw [add_ofNat_add]
      exact store8_other _ _ _ _ (hne _ (by omega))]
    exact h.globals i hi
  · intro j hj
    rw [hmem, h17]
    exact write8_byte (by omega) (by omega) (h.bytes j hj)
  · intro j hj
    rw [h17]
    exact h.mapped j hj
  · rw [h17, h18]
    exact h.below

theorem sim_store8 (F : Nat) (off : UInt32) : InstrSim P code F (.store8 off) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ D hcl _
  obtain ⟨h, g, hbs, hc1, hty0, hty1, hlt, hg, rfl, rfl⟩ := gen_store8 hgen
  have hU : P.normal P.uart = false := hcl.1 hbs
  have hh := hinv.len
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      obtain ⟨t1, t2, σ0, rfl⟩ : ∃ t1 t2 σ0, σ = t1 :: t2 :: σ0 := by
        match σ, hc1 with
        | t1 :: t2 :: σ0, _ => exact ⟨t1, t2, σ0, rfl⟩
      simp only [List.length_cons, Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero,
        show σ0.length + 1 + 1 - 2 = σ0.length by omega] at hlt hcode hc1 ⊢
      simp only [List.head?_cons, Option.some.injEq, List.getElem?_cons_succ,
        List.getElem?_cons_zero] at hty0 hty1
      subst hty0
      obtain ⟨v1, v2, vs, hvs⟩ : ∃ v1 v2 vs, sl.values = v1 :: v2 :: vs := by
        match hv : sl.values with
        | v1 :: v2 :: vs => exact ⟨v1, v2, vs, rfl⟩
        | [] => rw [hv] at hh; simp at hh
        | [_] => rw [hv] at hh; simp at hh
      have hstack := hinv.stack
      rw [hvs] at hstack
      have hty := hinv.types
      rw [hvs] at hty
      have hvl : vs.length = σ0.length := by rw [hvs] at hh; simpa using hh
      have hlt0 : σ0.length < 26 := by omega
      have htop : ValRel v1 (ms.x (regOf (σ0.length + 1))) := by
        have := hstack.top
        rwa [List.length_cons, hvl] at this
      have hadr : ValRel v2 (ms.x (regOf σ0.length)) := by
        have := hstack.pop.top
        rwa [hvl] at this
      obtain ⟨vv, rfl⟩ : ∃ vv, v1 = .i32 vv := by
        cases v1 <;> first | exact ⟨_, rfl⟩ | exact hty.1.elim
      have hvv : ms.x (regOf (σ0.length + 1)) = vv.toUInt64 := htop
      have hpg := hsr.pages
      have hcap := hsr.cap_lt
      generalize hn : (ms.x (regOf σ0.length)).toNat = n
      suffices key : ∀ y : UInt32, (n + off.toNat + 1 ≤ st.mem.pages * 65536 →
          y.toNat = n + off.toNat) →
          Outcome P code E ctl D (some σ0) (after a 7)
            (if n + off.toNat + 1 > st.mem.pages * 65536 then
              .Trap st "out of bounds memory access"
            else .Fallthrough { st with mem := st.mem.write8 y vv.toUInt8 }
              { sl with values := vs }) ms by
        rcases addr_cases hty.2.1 hty1 with ⟨x, rfl⟩ | ⟨x, rfl⟩
        · have hx : n = x.toNat := by rw [← hn, hadr]; simp
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x + off) fun hin => ?_
          rw [UInt32.toNat_add, ← hx]
          simp only [Nat.reducePow] at *
          omega
        · have hx : n = x.toNat := by rw [← hn, hadr]
          simp only [execOne.eq_def, hvs]
          rw [← hx]
          refine key (x.toUInt32 + off) fun hin => ?_
          rw [UInt32.toNat_add, UInt64.toNat_toUInt32, ← hx]
          simp only [Nat.reducePow] at *
          omega
      intro y hy
      have hr := regOf_lt_31 _ hlt0
      have hr16 : regOf σ0.length ≠ 16 := regOf_ne_scratch _ hlt0
      obtain ⟨s, hrs, hsps, hmems, houts, hxs, hpcs⟩ :=
        run_bounds8 P code (r := regOf σ0.length) h hr hr16 (CodeAt.take4' code hcode) hg hpc hsr
      rw [hn] at hpcs
      by_cases hin : n + off.toNat + 1 ≤ st.mem.pages * 65536
      · rw [ite_eq_right (by omega)]
        rw [ite_eq_left hin] at hpcs
        have c4 := hcode 4 (by simp)
        have c5 := hcode 5 (by simp)
        have c6 := hcode 6 (by simp)
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at c4 c5 c6
        let s5 : State := { s.setX 16 (s.x 17 + s.x (regOf σ0.length)) with pc := s.pc + 4 }
        have e5 : LeanExe.A64.exec P (.addReg 16 17 (regOf σ0.length)) s = some s5 := rfl
        have p5 : s5.pc = after a 5 := by
          show s.pc + 4 = _
          rw [hpcs, ← after_succ]
        have h16 : s5.x 16 = ms.x 17 + ms.x (regOf σ0.length) := by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x 16 = _
          rw [State.x_setX_same (by decide), hxs 17 (by decide), hxs _ hr16]
        have hk5 : ∀ q, q ≠ 16 → s5.x q = ms.x q := fun q hq => by
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).x q = _
          rw [State.x_setX_ne (Ne.symm hq), hxs q hq]
        let s6 : State :=
          { s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1)) with pc := s5.pc + 4 }
        have e6 : LeanExe.A64.exec P (.addImm 16 16 ⟨off.toNat + 1, by omega⟩) s5 = some s6 := by
          simp only [exec, State.xsp_eq_x (show (16 : Fin 32).val < 31 by decide),
            State.setXsp_eq_setX (show (16 : Fin 32).val < 31 by decide)]
          rfl
        have p6 : s6.pc = after a 6 := by
          show s5.pc + 4 = _
          rw [p5, ← after_succ]
        have hk6 : ∀ q, q ≠ 16 → s6.x q = ms.x q := fun q hq => by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).x q = _
          rw [State.x_setX_ne (Ne.symm hq), hk5 q hq]
        have h16' : s6.x 16 = ms.x 17 + ms.x (regOf σ0.length) + UInt64.ofNat (off.toNat + 1) := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).x 16 = _
          rw [State.x_setX_same (by decide), h16]
        have hbound : n + off.toNat + 1 ≤ E.cap * 65536 :=
          Nat.le_trans hin (Nat.mul_le_mul_right _ hpg.2)
        have hb : s6.x 16 + UInt64.ofNat (4095 : Fin 4096).val =
            ms.x 17 + UInt64.ofNat (4096 + y.toNat) := by
          show s6.x 16 + UInt64.ofNat 4095 = _
          rw [h16', byte_addr (by omega), hn, hy hin]
        have hex7 := exec_strb_base P (s := s6) (t := regOf (σ0.length + 1)) (imm := 4095) (n := 16)
          (by decide) (by
            rw [hb, hy hin]
            exact hsr.mapped _ (by unfold areaSize; omega)) hU
        have hmem6 : s6.mem = ms.mem := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).mem = _
          rw [State.setX_mem]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).mem = _
          rw [State.setX_mem, hmems]
        have hv6 : (s6.x (regOf (σ0.length + 1))).toUInt8 = vv.toUInt8 := by
          rw [hk6 _ (regOf_ne_scratch _ hlt), hvv]
          rfl
        let s7 : State := { s6 with
          mem := store8 s6.mem (s6.x 16 + UInt64.ofNat (4095 : Fin 4096).val)
            (s6.x (regOf (σ0.length + 1))).toUInt8, pc := s6.pc + 4 }
        have hr7 : Reach P code ms s7 :=
          hrs.trans (reach_exec P code (by rw [hpcs]; exact c4) e5
            (reach_exec P code (by rw [p5]; exact c5) e6
              (reach_exec P code (by rw [p6]; exact c6) hex7 (.refl _))))
        have hmem7 : s7.mem =
            store8 ms.mem (ms.x 17 + UInt64.ofNat (4096 + y.toNat)) vv.toUInt8 := by
          show store8 s6.mem _ _ = _
          rw [hmem6, hb, hv6]
        have hsp7 : s7.sp = ms.sp := by
          show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).sp = _
          rw [State.setX_sp]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).sp = _
          rw [State.setX_sp, hsps]
        have h187 : s7.x 18 = ms.x 18 := hk6 18 (by decide)
        have h177 : s7.x 17 = ms.x 17 := hk6 17 (by decide)
        have hlim : (ms.x 17 + UInt64.ofNat (4096 + y.toNat)).toNat < (ms.x 18).toNat := by
          rw [hsr.toNat_addr (j := 4096 + y.toNat) (by unfold areaSize; omega)]
          have := hsr.below
          unfold areaSize at this
          omega
        have hkeep : ∀ c : UInt64, (ms.x 18).toNat ≤ c.toNat → s7.mem c = ms.mem c := by
          intro c hc
          rw [hmem7]
          exact store8_other _ _ _ _ fun e => by rw [e] at hc; omega
        refine .inr ⟨_, rfl, s7, hr7, ?_, hsp7, ?_, h187, fun c hc => ?_, ?_,
          fun k hk => ?_, hsr.write8 P (hy := by rw [hy hin]; exact hin) h177 h187 hmem7⟩
        · show s6.pc + 4 = after a 7
          rw [p6, ← after_succ]
        · show (s5.setX 16 (s5.x 16 + UInt64.ofNat (off.toNat + 1))).io = _
          rw [State.setX_io]
          show (s.setX 16 (s.x 17 + s.x (regOf σ0.length))).io = _
          rw [State.setX_io, houts]
        · exact hkeep c (by
            have := hinv.frame.limit.2.1
            omega)
        · refine ⟨hstack.pop.pop.congr fun k hk => hk6 _ (regOf_ne_scratch k (by omega)),
            ?_, hinv.count, hinv.frame.congr hsp7 h187, hty.2.2, hinv.ltypes⟩
          intro i hi
          have hi' : i < E.localTypes.length := by rw [← hinv.count]; exact hi
          have hbound' := hinv.bound
          rw [hsp7, load64_congr (m := s7.mem) (m' := ms.mem) fun k hk => hkeep _ (by
            have := hinv.frame.limit
            rw [UInt64.toNat_add, toNat_slot, UInt64.toNat_ofNat']
            simp only [Nat.reducePow] at *
            omega)]
          exact hinv.locals i hi
        · exact hk6 _ (regOf_ne_scratch k (by omega))
      · rw [ite_eq_left (by omega)]
        rw [ite_eq_right hin] at hpcs
        exact .inr ⟨s, hrs, houts, .inr (.inl ⟨rfl, hpcs⟩)⟩

end LeanExe.A64
