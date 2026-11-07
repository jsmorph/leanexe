import LeanExe.M7.Proof.Slots

/-!
The simulation of the forms that write one operand slot: `local.get`, the constants, and the
operations on the values on top.  Each form's code is slot code that loads its operands into r0
to r3, computes in r0 to r7, and stores the result into the slot of its height, so its outcome
follows from `outcome_write`, the generator's inversion, and a lemma about the words that the
form's register code computes.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

theorem after_eq (a : UInt32) (n : Nat) : after a n = a + UInt32.ofNat (4 * n) := by
  rw [after, UInt32.ofNat_mul]
  rfl

/-- Proves an equation of addresses that `after` and numerals give, as `addr_eq` does. -/
macro "addr_after" : tactic => `(tactic| ((try simp only [after_eq]) <;> addr_eq))

theorem after_after (a : UInt32) (m n : Nat) : after (after a m) n = after a (m + n) := by
  rw [after_eq, after_eq, after_eq, add_ofNat_add]
  congr 2
  omega

theorem getElem?_reverse_cons {β : Type} {x : β} {l : List β} {h : Nat} (hh : h < l.length) :
    (x :: l).reverse[h]? = l.reverse[h]? := by
  rw [List.reverse_cons, List.getElem?_append_left (by simpa using hh)]

theorem getElem?_reverse_lt {β : Type} {l : List β} {h : Nat} {v : β}
    (hv : l.reverse[h]? = some v) : h < l.length := by
  have := (List.getElem?_eq_some_iff.mp hv).1
  simpa using this

/-! ## Register code -/

/-- A form of slot code that neither loads nor stores. -/
def Instr.regForm (i : Instr) : Bool := i.slotForm && i.slotOffset.isNone

/-- Register code keeps the memory, SP, LR, the device trace, and the read count. -/
theorem slotRun_reg {ops : List Instr} (h : ops.all Instr.regForm = true) (s : State) :
    (slotRun P σ ops s).mem = s.mem ∧ (slotRun P σ ops s).sp = s.sp ∧
      (slotRun P σ ops s).lr = s.lr := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i ops ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have hi := h.1
      simp only [Instr.regForm, Bool.and_eq_true, Option.isNone_iff_eq_none] at hi
      obtain ⟨he, -, -, -, -, -, -⟩ := exec_slotStep (P := P) (σ := σ) (s := s) hi.1
        (fun o ho => by rw [hi.2] at ho; cases ho)
      have hr : i.regOnly = true := by
        cases i <;> simp_all [Instr.slotForm, Instr.slotOffset]
      have k := exec_keeps hr he
      rw [slotRun_cons]
      obtain ⟨h1, h2, h3⟩ := ih h.2 (slotStep P σ i s)
      exact ⟨h1.trans k.mem, h2.trans k.sp, h3.trans k.lr⟩

theorem slotsOk_reg {ops : List Instr} (h : ops.all Instr.regForm = true) (sp : UInt32) :
    SlotsOk P sp ops := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Instr.regForm, Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact ⟨this.1, fun o ho => by rw [this.2] at ho; cases ho⟩

theorem slotsOk_append {sp : UInt32} {l1 l2 : List Instr} (h1 : SlotsOk P sp l1)
    (h2 : SlotsOk P sp l2) : SlotsOk P sp (l1 ++ l2) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h1 i hi
  · exact h2 i hi

theorem slotsOk_nil (sp : UInt32) : SlotsOk P sp [] := fun _ h => absurd h List.not_mem_nil

theorem slotsOk_cons {sp : UInt32} {i : Instr} {rest : List Instr} (hf : i.slotForm = true)
    (hw : ∀ o, i.slotOffset = some o → WordOk P (sp + UInt32.ofNat o))
    (hr : SlotsOk P sp rest) : SlotsOk P sp (i :: rest) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact ⟨hf, hw⟩
  · exact hr j hj

theorem slotsOk_ld {sp : UInt32} {t : Fin 8} {o : Nat} {h : o < 4096} {rest : List Instr}
    (hw : WordOk P (sp + UInt32.ofNat o)) (hr : SlotsOk P sp rest) :
    SlotsOk P sp (.ldrSp t ⟨o, h⟩ :: rest) := by
  refine slotsOk_cons rfl (fun o' ho => ?_) hr
  simp only [Instr.slotOffset, Option.some.injEq] at ho
  subst ho
  exact hw

theorem slotsOk_st {sp : UInt32} {t : Fin 8} {o : Nat} {h : o < 4096} {rest : List Instr}
    (hw : WordOk P (sp + UInt32.ofNat o)) (hr : SlotsOk P sp rest) :
    SlotsOk P sp (.strSp t ⟨o, h⟩ :: rest) := by
  refine slotsOk_cons rfl (fun o' ho => ?_) hr
  simp only [Instr.slotOffset, Option.some.injEq] at ho
  subst ho
  exact hw

theorem slotRun_st2 (w : State) (lo hi : Fin 8) (x : Nat) (h0 : x < 4096) (h1 : x + 4 < 4096) :
    (slotRun P σ [.strSp lo ⟨x, h0⟩, .strSp hi ⟨x + 4, h1⟩] w).mem =
      store32 (store32 w.mem (w.sp + UInt32.ofNat x) (w.r lo)) (w.sp + UInt32.ofNat (x + 4))
        (w.r hi) := rfl

/-! ## The outcome of a write -/

/-- The outcome of placed slot code whose memory afterwards is that of `ms` with the slot of
height `k` holding `r`, the top of the new stack `r :: vs`, where `vs` holds the values of the
heights below `k` in their slots. -/
theorem outcome_write {E : Env} {ctl : List Ctl} {σs σ' : List ValueType} {sl : Locals}
    {ms : State} {is : List Instr} {a : UInt32} {α : Type} {st : Store α} {k : Nat}
    {vs : List Value} {r : Value} {w0 w1 : UInt32} (hinv : Inv P E σs sl ms) (hpc : ms.pc = a)
    (hc : CodeAt code a is) (hok : SlotsOk P ms.sp is)
    (hmem : (slotRun P σ is ms).mem =
      store32 (store32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt k)) w0)
        (ms.sp + UInt32.ofNat (E.frame.opAt k + 4)) w1)
    (hk : k < E.frame.height) (hb : curBase ctl ≤ k) (hvs : vs.length = k)
    (hbelow : ∀ h v, vs.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v)
    (hr : SlotRel r w0 w1) (hty : Typed σ' (r :: vs)) :
    Outcome P σ code E ctl (some σ') (after a is.length)
      (.Fallthrough st { sl with values := r :: vs }) ms := by
  rw [← hpc] at hc
  obtain ⟨hr', hp, hsp, -, htr, hrd, -⟩ := run_slots (σ := σ) hok hc
  exact ⟨σ', rfl, _, hr', by rw [hp, hpc, after_eq], hsp, htr, hrd,
    keeps_write_op hinv.frame hmem hk, below_write_op hinv.frame hmem hk hb,
    Inv.write_op hinv hsp hmem hk hvs hbelow hr hty⟩

/-! ## `local.get` -/

theorem gen_localGet {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.localGet i) = .ok (is, fin)) :
    ∃ t src, E.localTypes[i]? = some t ∧ E.frame.localOff i = some src ∧
      σs.length < E.frame.height ∧ ∃ h0 h1 h2 h3,
        is = [.ldrSp 0 ⟨src, h0⟩, .ldrSp 1 ⟨src + 4, h1⟩,
          .strSp 0 ⟨E.frame.opAt σs.length, h2⟩, .strSp 1 ⟨E.frame.opAt σs.length + 4, h3⟩] ∧
        fin = some (t :: σs) := by
  unfold genInstr at hg
  split at hg
  · rename_i t ht
    simp only [except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨src, hsrc, dst, hdst, c, hc, rfl, rfl⟩ := hg
    obtain ⟨hlt, rfl⟩ := Env.op_ok hdst
    obtain ⟨h0, h1, h2, h3, rfl⟩ := copySlot_ok hc
    exact ⟨t, src, ht, Env.loc_ok hsrc, hlt, h0, h1, h2, h3, rfl, rfl⟩
  · exact absurd hg except_throw_ok

theorem sim_localGet (F i : Nat) : InstrSim P σ code F (.localGet i) := by
  intro E ctl σs a is fin hgen hcode _ _ hb α m st sl ms hinv hpc need D _ _ _
  obtain ⟨t, src, ht, hsrc, hlt, h0, h1, h2, h3, rfl, rfl⟩ := gen_localGet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hil : i < (sl.params ++ sl.locals).length := by
        rw [hinv.count]; exact (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨v, hv⟩ : ∃ v, (sl.params ++ sl.locals)[i]? = some v :=
        ⟨_, List.getElem?_eq_getElem hil⟩
      simp only [execOne.eq_def, ProofKit.Locals.get_append, hv]
      have hh := hinv.len
      obtain ⟨hs8, hsb, -, -⟩ := Frame.localOff_bounds hsrc
      obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
      have hok : SlotsOk P ms.sp [.ldrSp 0 ⟨src, h0⟩, .ldrSp 1 ⟨src + 4, h1⟩,
          .strSp 0 ⟨E.frame.opAt σs.length, h2⟩, .strSp 1 ⟨E.frame.opAt σs.length + 4, h3⟩] :=
        slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_st (hinv.frame.word (by omega) (by omega))
          (slotsOk_st (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _))))
      exact outcome_write hinv hpc hcode hok rfl hlt hb (by rw [hh]) hinv.stack
        (hinv.locals i v src hv hsrc) (Typed.cons (hinv.ltypes i v t src hv ht hsrc) hinv.types)


/-! ## `local.set` -/

theorem gen_localSet {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {i : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.localSet i) = .ok (is, fin)) :
    curBase ctl + 1 ≤ σs.length ∧ σs.head? = E.localTypes[i]? ∧
      σs.length - 1 < E.frame.height ∧ ∃ dst, E.frame.localOff i = some dst ∧ ∃ h0 h1 h2 h3,
        is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩, .strSp 0 ⟨dst, h2⟩,
          .strSp 1 ⟨dst + 4, h3⟩] ∧
        fin = some σs.tail := by
  unfold genInstr at hg
  by_cases hc : σs.length < curBase ctl + 1 ∨ σs.head? ≠ E.localTypes[i]?
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨src, hsrc, dst, hdst, c, hcp, rfl, rfl⟩ := hg
    obtain ⟨hlt, rfl⟩ := Env.op_ok hsrc
    obtain ⟨h0, h1, h2, h3, rfl⟩ := copySlot_ok hcp
    simp only [not_or, Ne, Decidable.not_not] at hc
    exact ⟨by omega, hc.2, hlt, dst, Env.loc_ok hdst, h0, h1, h2, h3, rfl, rfl⟩

theorem sim_localSet (F i : Nat) : InstrSim P σ code F (.localSet i) := by
  intro E ctl σs a is fin hgen hcode _ _ hb α m st sl ms hinv hpc need D _ _ _
  obtain ⟨hb1, hhead, hlt, dst, hdst, h0, h1, h2, h3, rfl, rfl⟩ := gen_localSet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      have hh := hinv.len
      obtain ⟨v, vs, hv⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hvs : sl.values with
        | nil => rw [hvs] at hh; simp at hh; omega
        | cons v vs => exact ⟨v, vs, rfl⟩
      obtain ⟨σ0, hti⟩ : ∃ t, E.localTypes[i]? = some t := by
        rw [← hhead]
        cases σs with
        | nil => simp at hb1
        | cons t _ => exact ⟨t, rfl⟩
      have hil : i < (sl.params ++ sl.locals).length := by
        rw [hinv.count]; exact (List.getElem?_eq_some_iff.mp hti).1
      obtain ⟨s', hs', hpl, hvals⟩ := ProofKit.Locals.set?_append sl i v hil
      simp only [execOne.eq_def, hv, hs']
      have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
      have htop := hinv.stack vs.length v (by
        rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
          Nat.sub_self, List.getElem?_cons_zero])
      rw [hvl] at htop
      have hty := hinv.types
      rw [hv] at hty
      obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
      obtain ⟨hd8, hdb, -, -⟩ := Frame.localOff_bounds hdst
      have hok : SlotsOk P ms.sp [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩, .strSp 0 ⟨dst, h2⟩,
          .strSp 1 ⟨dst + 4, h3⟩] :=
        slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (hinv.frame.word (by omega) (by omega))
          (slotsOk_st (hinv.frame.word (by omega) (by omega))
          (slotsOk_st (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _))))
      rw [← hpc] at hcode
      obtain ⟨hr', hp, hsp, -, htr, hrd, -⟩ := run_slots (σ := σ) hok hcode
      have hmem : (slotRun P σ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), h0⟩,
          .ldrSp 1 ⟨E.frame.opAt (σs.length - 1) + 4, h1⟩, .strSp 0 ⟨dst, h2⟩,
          .strSp 1 ⟨dst + 4, h3⟩] ms).mem =
          store32 (store32 ms.mem (ms.sp + UInt32.ofNat dst)
            (load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1)))))
            (ms.sp + UInt32.ofNat (dst + 4))
            (load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4))) := rfl
      obtain ⟨hk, hbl⟩ := keeps_write_local (b := curBase ctl) hinv.frame hmem hdst (by omega)
      exact ⟨σs.tail, rfl, _, hr', by rw [hp, hpc, after_eq], hsp, htr, hrd, hk, hbl,
        Inv.write_local hinv hsp hmem hdst hv hil hpl htop
          (fun ty hty' => by
            rw [hti, Option.some.injEq] at hty'
            subst hty'
            exact hty.head_cons (hhead.trans hti))
          hty.tail⟩

/-! ## Constants -/

theorem imm16_field {v : Nat} (hv : v < 65536) :
    imm16 (field 16 (v / 4096)) (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v) =
      UInt32.ofNat v := by
  simp only [imm16, field]
  congr 1
  omega

theorem movt_word {lo hi : Nat} (hlo : lo < 65536) (hhi : hi < 65536) :
    UInt32.ofNat lo &&& (0xFFFF : UInt32) ||| UInt32.ofNat hi <<< (16 : UInt32) =
      UInt32.ofNat (lo + hi * 65536) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, UInt32.toNat_and, toNat_shiftLeft32 _ 16 16 rfl (by decide)
      (by rw [UInt32.toNat_ofNat']; simp only [Nat.reducePow]; omega),
    UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    show (0xFFFF : UInt32).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : lo < 4294967296), Nat.mod_eq_of_lt (by omega : hi < 4294967296),
    Nat.mod_eq_of_lt (by omega : lo < 65536), show (65536 : Nat) = 2 ^ 16 from rfl,
    or_add_shift (by omega)]
  omega

theorem movConst_regForm (d : Fin 8) (w : Nat) : (movConst d w).all Instr.regForm = true := by
  unfold movConst; split <;> rfl

/-- `movConst d w` sets register `d` to `w` and keeps the other registers. -/
theorem slotRun_movConst (d : Fin 8) {w : Nat} (hw : w < 4294967296) (s : State) :
    (slotRun P σ (movConst d w) s).r d = UInt32.ofNat w ∧
      ∀ e, e ≠ d → (slotRun P σ (movConst d w) s).r e = s.r e := by
  unfold movConst
  split
  · rename_i h
    simp only [Instr.movwOf, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    refine ⟨by rw [State.r_withPc, State.r_setR_same, imm16_field h], fun e he => ?_⟩
    rw [State.r_withPc, State.r_setR_ne _ _ he]
  · rename_i h
    simp only [Instr.movwOf, Instr.movtOf, slotRun_cons, slotRun_nil, slotStep, exec,
      Option.getD_some]
    refine ⟨?_, fun e he => ?_⟩
    · rw [State.r_withPc, State.r_setR_same, State.r_withPc, State.r_setR_same,
        imm16_field (by omega), imm16_field (by omega), movt_word (by omega) (by omega)]
      congr 1
      omega
    · rw [State.r_withPc, State.r_setR_ne _ _ he, State.r_withPc, State.r_setR_ne _ _ he]

theorem toUInt32_ofNat_lo (v : UInt64) : UInt32.ofNat (v.toNat % 4294967296) = v.toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]
  simp only [Nat.reducePow, Nat.mod_mod]

theorem toUInt32_ofNat_hi (v : UInt64) :
    UInt32.ofNat (v.toNat / 4294967296) = (v >>> 32).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', toNat_hi64]

theorem gen_constI64 {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {v : UInt64}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.constI64 v) = .ok (is, fin)) :
    σs.length < E.frame.height ∧ ∃ h0 h1, is = movPair v ++
      [.strSp 0 ⟨E.frame.opAt σs.length, h0⟩, .strSp 1 ⟨E.frame.opAt σs.length + 4, h1⟩] ∧
      fin = some (.i64 :: σs) := by
  unfold genInstr at hg
  simp only [except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
  obtain ⟨dst, hdst, c, hc, rfl, rfl⟩ := hg
  obtain ⟨hlt, rfl⟩ := Env.op_ok hdst
  obtain ⟨h0, h1, rfl⟩ := stPair_ok hc
  exact ⟨hlt, h0, h1, rfl, rfl⟩

theorem sim_constI64 (F : Nat) (v : UInt64) : InstrSim P σ code F (.constI64 v) := by
  intro E ctl σs a is fin hgen hcode _ _ hb α m st sl ms hinv hpc need D _ _ _
  obtain ⟨hlt, h0, h1, rfl, rfl⟩ := gen_constI64 hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      simp only [execOne.eq_def]
      have hh := hinv.len
      obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
      have hreg : (movPair v).all Instr.regForm = true := by
        simp only [movPair, List.all_append, movConst_regForm, Bool.and_self]
      have hok : SlotsOk P ms.sp (movPair v ++
          [.strSp 0 ⟨E.frame.opAt σs.length, h0⟩, .strSp 1 ⟨E.frame.opAt σs.length + 4, h1⟩]) :=
        slotsOk_append (slotsOk_reg hreg _)
          (slotsOk_st (hinv.frame.word (by omega) (by omega))
          (slotsOk_st (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _)))
      have hv := v.toNat_lt_size
      obtain ⟨hm0, hm1, -⟩ := slotRun_reg (P := P) (σ := σ) hreg ms
      have e0 := slotRun_movConst (P := P) (σ := σ) 0 (w := v.toNat % 4294967296) (by omega) ms
      have e1 := slotRun_movConst (P := P) (σ := σ) 1 (w := v.toNat / 4294967296)
        (by simp only [UInt64.size] at hv; omega) (slotRun P σ (movConst 0 (v.toNat % 4294967296)) ms)
      refine outcome_write (w0 := (slotRun P σ (movPair v) ms).r 0)
        (w1 := (slotRun P σ (movPair v) ms).r 1) hinv hpc hcode hok ?_ hlt hb (by rw [hh])
        hinv.stack ?_ (Typed.cons trivial hinv.types)
      · rw [slotRun_append, slotRun_st2, hm0, hm1]
      · show _ ∧ _
        simp only [movPair, slotRun_append]
        rw [e1.1, e1.2 0 (by decide), e0.1, toUInt32_ofNat_lo, toUInt32_ofNat_hi]
        exact ⟨rfl, rfl⟩

/-! ## Operations on the two values on top -/

theorem gen_bin {E : Env} {ctl : List Ctl} {σs : List ValueType} {ops : List Instr}
    {res : Fin 8 × Fin 8} {t : ValueType} {is : List Instr} {fin : Option (List ValueType)}
    (hg : genBin E ctl σs ops res t = .ok (is, fin)) :
    curBase ctl + 2 ≤ σs.length ∧ σs.length - 1 < E.frame.height ∧ ∃ h0 h1 h2 h3 h4 h5,
      is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
        .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
        .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩,
        .ldrSp 3 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩] ++ ops ++
        [.strSp res.1 ⟨E.frame.opAt (σs.length - 2), h4⟩,
          .strSp res.2 ⟨E.frame.opAt (σs.length - 2) + 4, h5⟩] ∧
      fin = some (t :: σs.drop 2) := by
  unfold genBin at hg
  by_cases hc : σs.length < curBase ctl + 2
  · simp only [hc, ↓reduceIte, except_bind_ok] at hg
    obtain ⟨_, h, -⟩ := hg
    exact absurd h except_throw_ok
  · simp only [hc, ↓reduceIte, except_bind_ok, except_pure_ok, Prod.mk.injEq] at hg
    obtain ⟨x, hx, y, hy, l1, hl1, l2, hl2, l3, hl3, rfl, rfl⟩ := hg
    obtain ⟨-, rfl⟩ := Env.op_ok hx
    obtain ⟨hlt, rfl⟩ := Env.op_ok hy
    obtain ⟨h0, h1, rfl⟩ := ldPair_ok hl1
    obtain ⟨h2, h3, rfl⟩ := ldPair_ok hl2
    obtain ⟨h4, h5, rfl⟩ := stPair_ok hl3
    exact ⟨by omega, hlt, h0, h1, h2, h3, h4, h5, rfl, rfl⟩

theorem stack_top2 {vs : List Value} {x y : Value} :
    (y :: x :: vs).reverse[vs.length]? = some x ∧
      (y :: x :: vs).reverse[vs.length + 1]? = some y := by
  simp [List.reverse_cons]

/-- The words of the two `i64`s on top of a related stack. -/
theorem Inv.top2 {E : Env} {σs : List ValueType} {sl : Locals} {ms : State} {b a : UInt64}
    {vs : List Value} (hinv : Inv P E σs sl ms) (hv : sl.values = .i64 b :: .i64 a :: vs) :
    vs.length = σs.length - 2 ∧ 2 ≤ σs.length ∧
      load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 2))) = a.toUInt32 ∧
      load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 2) + 4)) =
        (a >>> 32).toUInt32 ∧
      load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))) = b.toUInt32 ∧
      load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1) + 4)) =
        (b >>> 32).toUInt32 := by
  have hh := hinv.len
  have hvl : vs.length = σs.length - 2 := by rw [hv] at hh; simp at hh; omega
  have h2 : 2 ≤ σs.length := by rw [hv] at hh; simp at hh; omega
  have hst := hinv.stack
  rw [hv] at hst
  have ha := hst vs.length (.i64 a) stack_top2.1
  have hbv := hst (vs.length + 1) (.i64 b) stack_top2.2
  rw [hvl] at ha
  rw [show vs.length + 1 = σs.length - 1 by omega] at hbv
  exact ⟨hvl, h2, ha.1, ha.2, hbv.1, hbv.2⟩

/-- The outcome of placed slot code that loads with `L`, computes with the register code `ops`,
and stores the pair `lo`, `hi` into the slot of the value below the top, when Talos replaces the
two `i64`s on top, `b` over `a`, by `r`, whose words the code computes. -/
theorem outcome_two {E : Env} {ctl : List Ctl} {σs : List ValueType} {sl : Locals} {ms : State}
    {a : UInt32} {α : Type} {st : Store α} {L ops : List Instr} {lo hi : Fin 8} {t : ValueType}
    {b a' : UInt64} {vs : List Value} {r : Value} {h4 : E.frame.opAt (σs.length - 2) < 4096}
    {h5 : E.frame.opAt (σs.length - 2) + 4 < 4096} (hinv : Inv P E σs sl ms) (hpc : ms.pc = a)
    (hcode : CodeAt code a (L ++ ops ++ [.strSp lo ⟨E.frame.opAt (σs.length - 2), h4⟩,
      .strSp hi ⟨E.frame.opAt (σs.length - 2) + 4, h5⟩]))
    (hb2 : curBase ctl + 2 ≤ σs.length) (hlt : σs.length - 1 < E.frame.height)
    (hL : SlotsOk P ms.sp L) (hLm : (slotRun P σ L ms).mem = ms.mem)
    (hLs : (slotRun P σ L ms).sp = ms.sp) (hops : ops.all Instr.regForm = true)
    (hv : sl.values = .i64 b :: .i64 a' :: vs)
    (hval : SlotRel r ((slotRun P σ ops (slotRun P σ L ms)).r lo)
      ((slotRun P σ ops (slotRun P σ L ms)).r hi))
    (htype : HasType t r) :
    Outcome P σ code E ctl (some (t :: σs.drop 2))
      (after a (L ++ ops ++ [Instr.strSp lo ⟨E.frame.opAt (σs.length - 2), h4⟩,
        Instr.strSp hi ⟨E.frame.opAt (σs.length - 2) + 4, h5⟩]).length)
      (.Fallthrough st { sl with values := r :: vs }) ms := by
  obtain ⟨hvl, -, -⟩ := hinv.top2 hv
  have hst := hinv.stack
  rw [hv] at hst
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds (k := σs.length - 2) (by omega)
  have hok := slotsOk_append (slotsOk_append hL (slotsOk_reg hops _))
    (slotsOk_st (P := P) (t := lo) (h := h4) (hinv.frame.word (by omega) (by omega))
    (slotsOk_st (t := hi) (h := h5) (hinv.frame.word (by omega) (by omega)) (slotsOk_nil _)))
  obtain ⟨hm, hsp, -⟩ := slotRun_reg (P := P) (σ := σ) hops (slotRun P σ L ms)
  refine outcome_write (w0 := (slotRun P σ ops (slotRun P σ L ms)).r lo)
    (w1 := (slotRun P σ ops (slotRun P σ L ms)).r hi) hinv hpc hcode hok ?_ (by omega)
    (by omega) hvl (fun h v hv' => ?_) hval (Typed.cons htype ?_)
  · rw [slotRun_append, slotRun_append, slotRun_st2, hm, hsp, hLm, hLs]
  · have hl := getElem?_reverse_lt hv'
    exact hst h v (by
      rw [getElem?_reverse_cons (by simp; omega), getElem?_reverse_cons hl]; exact hv')
  · have := hinv.types.drop 2
    rw [hv] at this
    simpa using this

/-- The simulation of a form that the generator compiles with `genBin`: the loads of the value
below the top into r0:r1 and of the top into r2:r3, the register code `ops`, and the store of the
pair `res`, when Talos replaces the two `i64`s on top by `op a b` for the lower `a` and the top
`b` and `ops` computes the words of `op a b`. -/
theorem sim_binary {inst : Instruction} {ops : List Instr} {res : Fin 8 × Fin 8} {t : ValueType}
    {op : UInt64 → UInt64 → Value}
    (hgen : ∀ E ctl σs a, genInstr E ctl σs a inst = genBin E ctl σs ops res t)
    (hops : ops.all Instr.regForm = true)
    (hfall : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals) (b a : UInt64)
      (vs : List Value), sl.values = .i64 b :: .i64 a :: vs →
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := op a b :: vs })
    (hinvalid : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∀ b a vs, sl.values ≠ .i64 b :: .i64 a :: vs) →
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg)
    (hval : ∀ (u : State) (a b : UInt64), u.r 0 = a.toUInt32 → u.r 1 = (a >>> 32).toUInt32 →
      u.r 2 = b.toUInt32 → u.r 3 = (b >>> 32).toUInt32 →
      SlotRel (op a b) ((slotRun P σ ops u).r res.1) ((slotRun P σ ops u).r res.2))
    (htype : ∀ a b, HasType t (op a b)) (F : Nat) : InstrSim P σ code F inst := by
  intro E ctl σs a is fin hg hcode _ _ hb α m st sl ms hinv hpc need D _ _ _
  rw [hgen] at hg
  obtain ⟨hb2, hlt, h0, h1, h2, h3, h4, h5, rfl, rfl⟩ := gen_bin hg
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      by_cases hshape : ∃ b a vs, sl.values = .i64 b :: .i64 a :: vs
      · obtain ⟨b, a', vs, hv⟩ := hshape
        rw [hfall f m st sl b a' vs hv]
        obtain ⟨-, -, ha0, ha1, hb0, hb1⟩ := hinv.top2 hv
        obtain ⟨hk8, hklr, -⟩ := E.frame.opAt_bounds (k := σs.length - 2) (by omega)
        obtain ⟨hj8, hjlr, hlrs⟩ := E.frame.opAt_bounds hlt
        exact outcome_two hinv hpc hcode hb2 hlt
          (slotsOk_ld (P := P) (t := 0) (h := h0) (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (t := 1) (h := h1) (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (t := 2) (h := h2) (hinv.frame.word (by omega) (by omega))
          (slotsOk_ld (t := 3) (h := h3) (hinv.frame.word (by omega) (by omega))
          (slotsOk_nil _))))) rfl rfl hops hv
          (hval (slotRun P σ [.ldrSp 0 ⟨E.frame.opAt (σs.length - 2), h0⟩,
            .ldrSp 1 ⟨E.frame.opAt (σs.length - 2) + 4, h1⟩,
            .ldrSp 2 ⟨E.frame.opAt (σs.length - 1), h2⟩,
            .ldrSp 3 ⟨E.frame.opAt (σs.length - 1) + 4, h3⟩] ms) a' b ha0 ha1 hb0 hb1)
          (htype a' b)
      · obtain ⟨msg, he⟩ := hinvalid f m st sl (fun b a vs h => hshape ⟨b, a, vs, h⟩)
        rw [he]
        trivial

/-- Talos's `Invalid` for an operand stack whose shape the form does not accept. -/
macro "invalid_tac" : tactic =>
  `(tactic| (
    intro f α m st sl hn
    simp only [execOne.eq_def]
    first
    | (split
       · rename_i b a vs hv
         exact absurd hv (hn b a vs)
       · exact ⟨_, rfl⟩)
    | exact ⟨_, rfl⟩))

theorem add_slot (a b : UInt64) :
    SlotRel (.i64 (a + b)) (addWithCarry a.toUInt32 b.toUInt32 false).1
      (addWithCarry (a >>> 32).toUInt32 (b >>> 32).toUInt32
        (addWithCarry a.toUInt32 b.toUInt32 false).2.1).1 := by
  have h := add_pair a.toUInt32 (a >>> 32).toUInt32 b.toUInt32 (b >>> 32).toUInt32
  rw [pairNat_toUInt32, pairNat_toUInt32,
    show (a.toNat + b.toNat) % 18446744073709551616 = (a + b).toNat by
      rw [UInt64.toNat_add]] at h
  exact eq_of_pairNat h

theorem sim_addI64 (F : Nat) : InstrSim P σ code F .addI64 :=
  sim_binary (inst := .addI64) (ops := [.addReg 1 0 0 2 0 0, .adcReg 1 1 3]) (res := (0, 1)) (t := .i64)
    (op := fun a b => .i64 (a + b)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
      state_simp
      rw [h0, h1, h2, h3, show 4 * (0 : Fin 8).val + (0 : Fin 4).val = 0 from rfl, shl_zero]
      exact add_slot a b)
    (fun _ _ => trivial) F

theorem sub_slot (a b : UInt64) :
    SlotRel (.i64 (a - b)) (addWithCarry a.toUInt32 (~~~b.toUInt32) true).1
      (addWithCarry (a >>> 32).toUInt32 (~~~(b >>> 32).toUInt32)
        (addWithCarry a.toUInt32 (~~~b.toUInt32) true).2.1).1 := by
  have h := (sub_pair a.toUInt32 (a >>> 32).toUInt32 b.toUInt32 (b >>> 32).toUInt32).1
  rw [pairNat_toUInt32, pairNat_toUInt32] at h
  apply eq_of_pairNat
  have hb : b.toNat < 18446744073709551616 := b.toNat_lt_size
  rw [h, UInt64.toNat_sub]
  simp only [Nat.reducePow]
  omega

theorem sim_subI64 (F : Nat) : InstrSim P σ code F .subI64 :=
  sim_binary (inst := .subI64) (ops := [.subReg 1 0 0 2, .sbcReg 0 1 1 3]) (res := (0, 1))
    (t := .i64) (op := fun a b => .i64 (a - b)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
      state_simp
      rw [h0, h1, h2, h3]
      exact sub_slot a b)
    (fun _ _ => trivial) F

theorem sim_andI64 (F : Nat) : InstrSim P σ code F .andI64 :=
  sim_binary (inst := .andI64) (ops := [.andReg 0 0 2, .andReg 1 1 3]) (res := (0, 1)) (t := .i64)
    (op := fun a b => .i64 (a &&& b)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
      state_simp
      rw [h0, h1, h2, h3]
      exact ⟨(UInt64.toUInt32_and a b).symm, by rw [UInt64.shiftRight_and, UInt64.toUInt32_and]⟩)
    (fun _ _ => trivial) F

theorem sim_orI64 (F : Nat) : InstrSim P σ code F .orI64 :=
  sim_binary (inst := .orI64) (ops := [.orrReg 0 0 0 2, .orrReg 0 1 1 3]) (res := (0, 1)) (t := .i64)
    (op := fun a b => .i64 (a ||| b)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
      state_simp
      rw [h0, h1, h2, h3]
      exact ⟨(UInt64.toUInt32_or a b).symm, by rw [UInt64.shiftRight_or, UInt64.toUInt32_or]⟩)
    (fun _ _ => trivial) F

theorem sim_xorI64 (F : Nat) : InstrSim P σ code F .xorI64 :=
  sim_binary (inst := .xorI64) (ops := [.eorReg 0 0 2, .eorReg 1 1 3]) (res := (0, 1)) (t := .i64)
    (op := fun a b => .i64 (a ^^^ b)) (fun _ _ _ _ => rfl) rfl
    (fun f α m st sl b a vs hv => by simp only [execOne.eq_def, hv]) (by invalid_tac)
    (fun u a b h0 h1 h2 h3 => by
      simp only [slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
      state_simp
      rw [h0, h1, h2, h3]
      exact ⟨(UInt64.toUInt32_xor a b).symm, by rw [UInt64.shiftRight_xor, UInt64.toUInt32_xor]⟩)
    (fun _ _ => trivial) F

end LeanExe.M7
