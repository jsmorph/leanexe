import LeanExe.A64.Proof.Straight

/-!
The simulation of the instructions that can trap: `unreachable`, `remUI64`, and `divUI64`.  A
trap branches to the stub of its code, and `branchField_target` shows that an encoded branch
reaches the target that the generator gave it.  `CBZ` of the divisor reaches the stub of a
division by zero exactly when Talos traps, and otherwise `UDIV`, with `MSUB` for the remainder,
computes Talos's result, since `a - a / b * b = a % b`.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## Branch offsets -/

/-- A branch field that the generator encodes takes the branch to its target. -/
theorem branchField_target {bits : Nat} {here target : UInt64} {f : Nat}
    (hbits : bits = 19 ∨ bits = 26) (h : branchField bits here target = .ok f) :
    f < 2 ^ bits ∧ here + sext bits f * 4 = target := by
  unfold branchField at h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hc
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have ht := target.toNat_lt
    have hh := here.toNat_lt
    have hpos : (2 : Int) ^ bits ≠ 0 := by rcases hbits with rfl | rfl <;> decide
    have hf := Int.toNat_of_nonneg
      (Int.emod_nonneg ((Int.ofNat target.toNat - Int.ofNat here.toNat) / 4) hpos)
    have h4 : (4 : UInt64).toNat = 4 := rfl
    generalize hd : Int.ofNat target.toNat - Int.ofNat here.toNat = d at hc hf ⊢
    generalize hn : (d / 4 % 2 ^ bits).toNat = n at hf ⊢
    simp only [Int.ofNat_eq_natCast] at hd
    rcases hbits with rfl | rfl <;>
    · simp only [Nat.reducePow, Int.reducePow, Nat.add_one_sub_one] at hc hf ⊢
      refine ⟨by omega, ?_⟩
      apply UInt64.toNat_inj.mp
      unfold sext
      split
      · rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', h4]
        simp only [Nat.reducePow]
        omega
      · rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_ofNat',
          UInt64.toNat_ofNat', h4]
        simp only [Nat.reducePow]
        omega

theorem bField_target {here target : UInt64} {f : Fin 67108864}
    (h : bField here target = .ok f) : here + sext 26 f.val * 4 = target := by
  unfold bField at h
  cases hb : branchField 26 here target with
  | error e => simp [hb, bind, Except.bind] at h
  | ok n =>
      simp [hb, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨hlt, ht⟩ := branchField_target (.inr rfl) hb
      subst h
      simpa [Nat.mod_eq_of_lt hlt] using ht

theorem cbField_target {here target : UInt64} {f : Fin 524288}
    (h : cbField here target = .ok f) : here + sext 19 f.val * 4 = target := by
  unfold cbField at h
  cases hb : branchField 19 here target with
  | error e => simp [hb, bind, Except.bind] at h
  | ok n =>
      simp [hb, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨hlt, ht⟩ := branchField_target (.inl rfl) hb
      subst h
      simpa [Nat.mod_eq_of_lt hlt] using ht

/-! ## Results that replace operands -/

/-- The outcome of an instruction whose result `v`, which `w` holds, replaces its operands above
`vs` in the register of height `vs.length`, after code that ends at `endA`. -/
theorem res_outcome {E : Env} {ctl : List Ctl} {D : Nat} {endA : UInt64} {α : Type} {st : Store α}
    {sl : Locals} {ms ms' : State} {vs : List Value} {v : Value} {w : UInt64}
    {σ0 σr : List ValueType} {t : ValueType} (hv : ValRel v w) (ht : HasType t v)
    (hty : Typed σr vs) (hinv : Inv P E.localTypes σ0 sl ms)
    (hsr : StoreRel P E.cap E.globalTypes st ms) (hb : curBase ctl ≤ vs.length)
    (hlt : vs.length < 26) (hstack : StackRel ms vs) (hr : Reach P code ms ms')
    (hpc : ms'.pc = endA) (hx : ms'.x (regOf vs.length) = w)
    (hkeep : ∀ k < vs.length, ms'.x (regOf k) = ms.x (regOf k)) (h18 : ms'.x 18 = ms.x 18)
    (h17 : ms'.x 17 = ms.x 17) (hsp : ms'.sp = ms.sp) (hmem : ms'.mem = ms.mem)
    (hout : ms'.out = ms.out) :
    Outcome P code E ctl D (some (t :: σr)) endA
      (.Fallthrough st { sl with values := v :: vs }) ms := by
  refine .inr ⟨_, rfl, ms', hr, hpc, hsp, hout, h18, fun b _ => by rw [hmem], ?_,
    fun j hj => hkeep j (by omega), hsr.regs h17 h18 hmem⟩
  exact ⟨StackRel.push hstack hlt (by rw [hx]; exact hv) hkeep, hinv.locals.congr hmem hsp,
    hinv.count, hinv.frame.congr hsp h18, Typed.cons ht hty, hinv.ltypes⟩

theorem sub_div_mul_eq_mod (a b : UInt64) : a - a / b * b = a % b := by
  apply UInt64.toNat_inj.mp
  have h1 := Nat.div_mul_le_self a.toNat b.toNat
  have h2 := a.toNat_lt
  have hle : a / b * b ≤ a := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mul, UInt64.toNat_div, Nat.mod_eq_of_lt (by omega)]
    exact h1
  rw [UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod,
    Nat.mod_eq_of_lt (by omega)]
  have h3 := Nat.mod_add_div a.toNat b.toNat
  rw [Nat.mul_comm] at h3
  omega

/-! ## Traps -/

theorem gen_unreachable {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a .unreachable = .ok (is, fin)) :
    ∃ f, bField a E.trapUnreachable = .ok f ∧ is = [.b f] ∧ fin = none := by
  cases hb : bField a E.trapUnreachable with
  | error e => simp [genInstr, hb, bind, Except.bind] at hg
  | ok f =>
      simp [genInstr, hb, bind, Except.bind, pure, Except.pure] at hg
      exact ⟨f, rfl, hg.1.symm, hg.2.symm⟩

theorem sim_unreachable (F : Nat) : InstrSim P code F .unreachable := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨f, hf, rfl, rfl⟩ := gen_unreachable hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ k =>
      simp only [execOne.eq_def]
      have hc : code ms.pc = some (encode (.b f)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      refine .inr ⟨{ ms with pc := ms.pc + sext 26 f.val * 4 },
        reach_exec P code hc rfl (.refl _), rfl, .inl ⟨rfl, ?_⟩⟩
      show ms.pc + sext 26 f.val * 4 = E.trapUnreachable
      rw [hpc]; exact bField_target hf

theorem gen_divrem {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64}
    {is : List Instr} {fin : Option (List ValueType)} {inst : Instruction}
    {rest : Fin 32 → Fin 32 → List Instr}
    (hinst : (inst = .remUI64 ∧ rest = fun x y => [.udiv scratch x y, .msub x scratch y x]) ∨
      (inst = .divUI64 ∧ rest = fun x y => [.udiv x x y]))
    (hg : genInstr E ctl σ a inst = .ok (is, fin)) :
    curBase ctl + 2 ≤ σ.length ∧ σ.length - 1 < 26 ∧ ∃ f, cbField a E.trapDiv = .ok f ∧
      is = .cbz (regOf (σ.length - 1)) f :: rest (regOf (σ.length - 2)) (regOf (σ.length - 1)) ∧
      fin = some (.i64 :: σ.drop 2) := by
  by_cases hc : σ.length < curBase ctl + 2
  · rcases hinst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : σ.length - 1 < 26
  · cases hcb : cbField a E.trapDiv with
    | error e =>
        rcases hinst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [genInstr, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), hcb, bind,
            Except.bind] at hg
    | ok f =>
        rcases hinst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [genInstr, hc, opReg_ok hlt, opReg_ok (show σ.length - 2 < 26 by omega), hcb, bind,
            Except.bind, pure, Except.pure] at hg <;>
          exact ⟨by omega, hlt, f, rfl, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : σ.length - 2 < 26
    · rcases hinst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [genInstr, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      rcases hinst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [genInstr, hc, he2, bind, Except.bind] at hg

/-- `CBZ` of a zero divisor reaches the stub of a division by zero. -/
theorem cbz_taken {ms : State} {a target : UInt64} {r : Fin 32} {f : Fin 524288}
    (hc : code ms.pc = some (encode (.cbz r f))) (hpc : ms.pc = a)
    (hf : cbField a target = .ok f) (h0 : ms.x r = 0) :
    Reach P code ms { ms with pc := target } := by
  refine reach_exec P code hc ?_ (.refl _)
  simp only [exec, h0, ite_true]
  rw [hpc, cbField_target hf]

/-- `CBZ` of a nonzero divisor falls through. -/
theorem cbz_next {ms : State} {r : Fin 32} {f : Fin 524288} (h0 : ms.x r ≠ 0) :
    LeanExe.A64.exec P (.cbz r f) ms = some { ms with pc := ms.pc + 4 } := by
  simp [exec, h0]

/-- The simulation of a division or remainder, whose code is a `CBZ` of the divisor `y` to the
stub of a division by zero followed by `rest x y`, which leaves `op a b` in the register `x` of
the dividend and changes no other register but the scratch register. -/
theorem sim_divrem_of {F : Nat} {inst : Instruction} {rest : Fin 32 → Fin 32 → List Instr}
    (op : UInt64 → UInt64 → UInt64)
    (hinst : (inst = .remUI64 ∧ rest = fun x y => [.udiv scratch x y, .msub x scratch y x]) ∨
      (inst = .divUI64 ∧ rest = fun x y => [.udiv x x y]))
    (hrun : ∀ (ms : State) (a' : UInt64) (x y : Fin 32), x.val < 31 → x ≠ scratch →
      y ≠ scratch → x ≠ y → CodeAt code a' (rest x y) → ms.pc = a' →
      ∃ ms', Reach P code ms ms' ∧ ms'.pc = after a' (rest x y).length ∧
        ms'.x x = op (ms.x x) (ms.x y) ∧ (∀ q, q ≠ x → q ≠ scratch → ms'.x q = ms.x q) ∧
        ms'.sp = ms.sp ∧ ms'.mem = ms.mem ∧ ms'.out = ms.out)
    (hexec : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ b a vs, sl.values = .i64 b :: .i64 a :: vs ∧
        execOne (f + 1) m st sl inst = if b = 0 then .Trap st "integer divide by zero"
          else .Fallthrough st { sl with values := .i64 (op a b) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨hhb, hlt, f, hf, rfl, rfl⟩ := gen_divrem hinst hgen
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at *
  cases F with
  | zero =>
      rcases hinst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [execOne.eq_def, Outcome, or_true]
  | succ k =>
      rcases hexec k m st sl with ⟨b, a', vs, hvs, hex⟩ | ⟨msg, hex⟩
      · rw [hex]
        have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        rw [hvs] at hty
        have hy : ms.x (regOf (h - 1)) = b := by
          have := hst.top; rw [show (Value.i64 a' :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = a' := by
          have := hst.pop.top; rw [hvl] at this; exact this
        have hc : code ms.pc = some (encode (.cbz (regOf (h - 1)) f)) := by
          rw [hpc]; exact (CodeAt.cons.mp hcode).1
        split
        · rename_i hb0
          exact .inr ⟨_, cbz_taken P code hc hpc hf (by rw [hy, hb0]), rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
        · rename_i hb0
          have hstep := reach_exec P code hc (cbz_next P (by rw [hy]; exact hb0)) (.refl _)
          have hrest := (CodeAt.cons.mp hcode).2
          have hne : regOf (h - 2) ≠ regOf (h - 1) := fun e =>
            absurd (regOf_inj (h - 2) (by omega) (h - 1) hlt e) (by omega)
          obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
            hrun { ms with pc := ms.pc + 4 } (after a 1) (regOf (h - 2)) (regOf (h - 1))
              (regOf_lt_31 _ (by omega)) (regOf_ne_scratch _ (by omega))
              (regOf_ne_scratch _ hlt) hne hrest (by simp [hpc, after])
          apply res_outcome P code (vs := vs) (v := .i64 (op a' b)) (w := op a' b) (t := .i64) rfl
            trivial
            (hty.drop 2) hinv hsr (by omega) (by omega)
            hst.pop.pop (hstep.trans hr) _ _ _
            (hkeep 18 (Ne.symm (regOf_ne_18 _ (by omega))) (by decide))
            (hkeep 17 (Ne.symm (regOf_ne_17 _ (by omega))) (by decide)) hsp hmem hout
          · rw [hp, after_after, List.length_cons, Nat.add_comm]
          · rw [hvl, hres]; simp [hx, hy]
          · intro j hj
            rw [hkeep _ (fun e => absurd (regOf_inj j (by omega) (h - 2) (by omega) e) (by omega))
              (regOf_ne_scratch j (by omega))]
            rfl
      · rw [hex]; exact .inr trivial

theorem sim_remUI64 (F : Nat) : InstrSim P code F .remUI64 := by
  refine sim_divrem_of P code (fun a b => a % b) (.inl ⟨rfl, rfl⟩) ?_ ?_
  · intro ms a' x y hx hxs hys hxy hcode hpc
    have c0 := hcode 0 (by simp)
    have c1 := hcode 1 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1
    let s1 : State := { ms.setX scratch (ms.x x / ms.x y) with pc := ms.pc + 4 }
    have p1 : s1.pc = after a' 1 := by simp [s1, hpc, after]
    refine ⟨{ s1.setX x (s1.x x - s1.x scratch * s1.x y) with pc := s1.pc + 4 },
      reach_exec P code (by rw [hpc]; exact c0) rfl
        (reach_exec P code (by rw [p1]; exact c1) rfl (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s1.pc + 4 = after a' 2; rw [p1]; exact (after_succ a' 1).symm
    · rw [State.x_withPc, State.x_setX_same hx]
      have e1 : s1.x x = ms.x x := State.x_setX_ne (s := ms) (Ne.symm hxs)
      have e2 : s1.x scratch = ms.x x / ms.x y := State.x_setX_same (s := ms) (by decide)
      have e3 : s1.x y = ms.x y := State.x_setX_ne (s := ms) (Ne.symm hys)
      rw [e1, e2, e3, sub_div_mul_eq_mod]
    · intro q hq hqs
      rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
      exact State.x_setX_ne (s := ms) (Ne.symm hqs)
    · show (s1.setX x _).sp = ms.sp; rw [State.setX_sp]; exact State.setX_sp
    · show (s1.setX x _).mem = ms.mem; rw [State.setX_mem]; exact State.setX_mem
    · show (s1.setX x _).out = ms.out; rw [State.setX_out]; exact State.setX_out
  · intro f α m st sl
    cases hv : sl.values with
    | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
    | cons v vs =>
        cases v with
        | i64 b =>
            cases vs with
            | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
            | cons u us =>
                cases u with
                | i64 a => exact .inl ⟨b, a, us, rfl, by simp only [execOne.eq_def, hv]⟩
                | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
        | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩

theorem sim_divUI64 (F : Nat) : InstrSim P code F .divUI64 := by
  refine sim_divrem_of P code (fun a b => a / b) (.inr ⟨rfl, rfl⟩) ?_ ?_
  · intro ms a' x y hx hxs hys hxy hcode hpc
    have c0 := hcode 0 (by simp)
    simp only [List.getElem_cons_zero, after_zero] at c0
    refine ⟨{ ms.setX x (ms.x x / ms.x y) with pc := ms.pc + 4 },
      reach_exec P code (by rw [hpc]; exact c0) rfl (.refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show ms.pc + 4 = after a' 1; simp [hpc, after]
    · rw [State.x_withPc, State.x_setX_same hx]
    · intro q hq _
      rw [State.x_withPc, State.x_setX_ne (Ne.symm hq)]
    · exact State.setX_sp
    · exact State.setX_mem
    · exact State.setX_out
  · intro f α m st sl
    cases hv : sl.values with
    | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
    | cons v vs =>
        cases v with
        | i64 b =>
            cases vs with
            | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
            | cons u us =>
                cases u with
                | i64 a => exact .inl ⟨b, a, us, rfl, by simp only [execOne.eq_def, hv]⟩
                | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
        | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩

end LeanExe.A64
