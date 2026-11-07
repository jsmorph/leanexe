import LeanExe.A64.Proof.Traps

/-!
The simulation of the branches `br`, `br_if`, and `ret`.  A branch to a construct moves the
value that it carries, if any, from the top of the stack to the register of the construct's base
height with `ORR` and branches with `B` to the construct's target, so the machine reaches the
target with the carried value where the construct's code after the target expects it and with the
registers below the base unchanged.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

theorem gen_branchTo {t : Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    (hg : branchTo t σ a = .ok is) :
    t.base + t.arity ≤ σ.length ∧ t.arity ≤ 1 ∧ σ.take t.arity = t.types ∧
      (t.arity = 1 → σ.length - 1 < 26 ∧ t.base < 26) ∧
      ∃ f, bField (after a t.arity) t.target = .ok f ∧
        is = (if t.arity = 1 then [mov (regOf t.base) (regOf (σ.length - 1))] else []) ++
          [.b f] := by
  obtain ⟨tg, ts, bs⟩ := t
  unfold branchTo at hg
  simp only [Ctl.arity] at hg ⊢
  by_cases hc : σ.length < bs + ts.length ∨ ts.length > 1 ∨ σ.take ts.length ≠ ts
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have htake : σ.take ts.length = ts :=
    Classical.byContradiction fun hne => hc (.inr (.inr hne))
  refine ⟨by omega, by omega, htake, ?_⟩
  generalize hσl : σ.length = h at hg hc ⊢
  by_cases h1 : ts.length = 1
  · simp only [h1] at hg htake hc ⊢
    have hlt : ¬ h < bs + 1 := by omega
    by_cases hb : bs < 26
    · by_cases hh : h - 1 < 26
      · cases hf : bField (after a 1) tg with
        | error e =>
            simp [hlt, htake, opReg_ok hb, opReg_ok hh, hf, bind, Except.bind, pure,
              Except.pure] at hg
        | ok f =>
            simp [hlt, htake, opReg_ok hb, opReg_ok hh, hf, bind, Except.bind, pure,
              Except.pure] at hg
            subst hg
            exact ⟨fun _ => ⟨hh, hb⟩, f, rfl, by simp⟩
      · obtain ⟨e, he⟩ := opReg_error hh
        simp [hlt, htake, opReg_ok hb, he, bind, Except.bind] at hg
    · obtain ⟨e, he⟩ := opReg_error hb
      simp [hlt, htake, he, bind, Except.bind] at hg
  · have h0 : ts.length = 0 := by omega
    simp only [h0] at hg htake hc ⊢
    have hlt : ¬ h < bs := by omega
    cases hf : bField (after a 0) tg with
    | error e => simp [hlt, htake, hf, bind, Except.bind, pure, Except.pure] at hg
    | ok f =>
        simp [hlt, htake, hf, bind, Except.bind, pure, Except.pure] at hg
        subst hg
        exact ⟨fun e => absurd e (by decide), f, rfl, by simp⟩

/-- The run of a branch to `t` from a related state whose stack `vs` has its height `h`: the
machine reaches `t.target` with the value that the branch carries in the register of `t.base`
and the registers below `t.base`, `SP`, the memory, and the UART's output unchanged. -/
theorem run_branchTo {t : Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    {ms : State} {vs : List Value} (hg : branchTo t σ a = .ok is) (hcode : CodeAt code a is)
    (hpc : ms.pc = a) (hst : StackRel ms vs) (hh : vs.length = σ.length) (hty : Typed σ vs) :
    ∃ ms', Reach P code ms ms' ∧ ms'.pc = t.target ∧ Kept t vs ms' ∧ Frame t.base ms ms' ∧
      ms'.x 18 = ms.x 18 ∧ ms'.x 17 = ms.x 17 ∧ ms'.sp = ms.sp ∧ ms'.mem = ms.mem ∧
      ms'.out = ms.out := by
  obtain ⟨hle, ha1, htake, hregs, f, hf, rfl⟩ := gen_branchTo hg
  have hkt : Typed t.types (vs.take t.arity) := by rw [← htake]; exact hty.take t.arity
  generalize hσl : σ.length = h at hle hregs hh hcode ⊢
  have h26 := hst.1
  by_cases h1 : t.arity = 1
  · obtain ⟨hh1, hb⟩ := hregs h1
    simp only [h1, ite_true, List.singleton_append] at hcode
    have c0 := (CodeAt.cons.mp hcode).1
    have c1 := (CodeAt.cons.mp (CodeAt.cons.mp hcode).2).1
    let s1 : State := { ms.setX (regOf t.base) (ms.x 31 ||| ms.x (regOf (h - 1))) with
      pc := ms.pc + 4 }
    have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
    have hx31 : ms.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
    refine ⟨{ s1 with pc := s1.pc + sext 26 f.val * 4 },
      reach_exec P code (by rw [hpc]; exact c0) rfl
        (reach_exec P code (by rw [p1]; exact c1) rfl (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
    · show s1.pc + sext 26 f.val * 4 = t.target
      rw [p1, ← bField_target hf, h1]
    · refine ⟨by omega, by omega, fun j hj => ?_, hkt⟩
      have hj0 : j = 0 := by omega
      subst hj0
      show ValRel _ ((ms.setX (regOf t.base) (ms.x 31 ||| ms.x (regOf (h - 1)))).x
        (regOf (t.base + 0)))
      rw [Nat.add_zero, State.x_setX_same (regOf_lt_31 _ hb), hx31, UInt64.zero_or]
      have htop := hst.2 (h - 1) (by omega)
      have : vs.reverse[h - 1]'(by simp; omega) = vs[0]'(by omega) := by
        rw [List.getElem_reverse]; congr 1; omega
      rw [this] at htop
      simpa [h1] using htop
    · intro k hk
      show (ms.setX (regOf t.base) _).x (regOf k) = ms.x (regOf k)
      exact State.x_setX_ne (fun e => absurd (regOf_inj t.base hb k (by omega) e) (by omega))
    · show (ms.setX (regOf t.base) _).x 18 = ms.x 18
      exact State.x_setX_ne (regOf_ne_18 _ hb)
    · show (ms.setX (regOf t.base) _).x 17 = ms.x 17
      exact State.x_setX_ne (regOf_ne_17 _ hb)
    · show (ms.setX (regOf t.base) _).sp = ms.sp; exact State.setX_sp
    · show (ms.setX (regOf t.base) _).mem = ms.mem; exact State.setX_mem
    · show (ms.setX (regOf t.base) _).out = ms.out; exact State.setX_out
  · have h0 : t.arity = 0 := by omega
    simp only [h1, ite_false, List.nil_append] at hcode
    have c0 := (CodeAt.cons.mp hcode).1
    refine ⟨{ ms with pc := ms.pc + sext 26 f.val * 4 },
      reach_exec P code (by rw [hpc]; exact c0) rfl (.refl _), ?_, ?_, fun _ _ => rfl, rfl, rfl,
      rfl, rfl, rfl⟩
    · show ms.pc + sext 26 f.val * 4 = t.target
      rw [hpc, ← bField_target hf, h0, after_zero]
    · exact ⟨by omega, by omega, fun j hj => absurd hj (by omega), hkt⟩

/-! ## Outcomes of branches -/

/-- The outcome of a branch `k` levels out to `t` that reaches `t.target` with the values that it
carries kept and the locals unchanged. -/
theorem break_outcome {E : Env} {ctl : List Ctl} {D : Nat} {fin : Option (List ValueType)}
    {endA : UInt64} {α : Type} {st : Store α} {sl sl' : Locals} {ms ms' : State} {k : Nat}
    {t : Ctl} {σ : List ValueType} (ht : ctl[k]? = some t) (hinv : Inv P E.localTypes σ sl ms)
    (hsr : StoreRel P E.cap E.globalTypes st ms)
    (hl : sl'.params ++ sl'.locals = sl.params ++ sl.locals) (hr : Reach P code ms ms')
    (hpc : ms'.pc = t.target) (hk : Kept t sl'.values ms') (hf : Frame t.base ms ms')
    (h18 : ms'.x 18 = ms.x 18) (h17 : ms'.x 17 = ms.x 17) (hsp : ms'.sp = ms.sp)
    (hmem : ms'.mem = ms.mem) (hout : ms'.out = ms.out) :
    Outcome P code E ctl D fin endA (.Break k st sl') ms :=
  .inr ⟨t, ht, ms', hr, hpc, hsp, hout, h18, fun _ _ => by rw [hmem],
    by rw [hl]; exact hinv.locals.congr hmem hsp, by rw [hl]; exact hinv.ltypes, hk, hf,
    hsr.regs h17 h18 hmem⟩

/-- Popping the top of the stack of a related state and moving its program counter. -/
theorem Inv.pop {lts σ : List ValueType} {sl : Locals} {ms : State} {v : Value}
    {vs : List Value} (hinv : Inv P lts σ sl ms) (hv : sl.values = v :: vs) (p : UInt64) :
    Inv P lts σ.tail { sl with values := vs } { ms with pc := p } := by
  have hst := hinv.stack
  rw [hv] at hst
  have hty := hinv.types
  rw [hv] at hty
  exact ⟨hst.pop.congr fun _ _ => rfl, hinv.locals.congr rfl rfl, hinv.count,
    hinv.frame.congr rfl rfl, hty.tail, hinv.ltypes⟩

/-- `CBNZ` of a nonzero register branches. -/
theorem cbnz_taken {ms : State} {a target : UInt64} {r : Fin 32} {f : Fin 524288}
    (hc : code ms.pc = some (encode (.cbnz r f))) (hpc : ms.pc = a)
    (hf : cbField a target = .ok f) (h0 : ms.x r ≠ 0) :
    Reach P code ms { ms with pc := target } := by
  refine reach_exec P code hc ?_ (.refl _)
  simp only [exec, ne_eq, h0, not_false_eq_true, ite_true]
  rw [hpc, cbField_target hf]

/-- `CBNZ` of a zero register falls through. -/
theorem cbnz_next {ms : State} {r : Fin 32} {f : Fin 524288} (h0 : ms.x r = 0) :
    LeanExe.A64.exec P (.cbnz r f) ms = some { ms with pc := ms.pc + 4 } := by
  simp [exec, h0]

/-! ## `br` and `ret` -/

theorem gen_br {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {n : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.br n) = .ok (is, fin)) :
    ∃ t, ctl[n]? = some t ∧ branchTo t σ a = .ok is ∧ fin = none := by
  cases ht : ctl[n]? with
  | none => simp [genInstr, ht, throw, throwThe, MonadExceptOf.throw] at hg
  | some t =>
      cases hb : branchTo t σ a with
      | error e => simp [genInstr, ht, hb, bind, Except.bind] at hg
      | ok bs =>
          simp [genInstr, ht, hb, bind, Except.bind, pure, Except.pure] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨t, rfl, hb, rfl⟩

theorem gen_ret {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genInstr E ctl σ a .ret = .ok (is, fin)) :
    ∃ t, ctl.getLast? = some t ∧ branchTo t σ a = .ok is ∧ fin = none := by
  cases ht : ctl.getLast? with
  | none => simp [genInstr, ht, throw, throwThe, MonadExceptOf.throw] at hg
  | some t =>
      cases hb : branchTo t σ a with
      | error e => simp [genInstr, ht, hb, bind, Except.bind] at hg
      | ok bs =>
          simp [genInstr, ht, hb, bind, Except.bind, pure, Except.pure] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨t, rfl, hb, rfl⟩

theorem sim_br (F n : Nat) : InstrSim P code F (.br n) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨t, ht, hbr, rfl⟩ := gen_br hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      simp only [execOne.eq_def]
      obtain ⟨ms', hr, hp, hk, hfr, h18, h17, hsp, hmem, hout⟩ :=
        run_branchTo P code hbr hcode hpc hinv.stack hinv.len hinv.types
      exact break_outcome P code ht hinv hsr rfl hr hp hk hfr h18 h17 hsp hmem hout

theorem sim_ret (F : Nat) : InstrSim P code F .ret := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨t, ht, hbr, rfl⟩ := gen_ret hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      simp only [execOne.eq_def]
      obtain ⟨ms', hr, hp, hk, -, h18, h17, hsp, hmem, hout⟩ :=
        run_branchTo P code hbr hcode hpc hinv.stack hinv.len hinv.types
      exact .inr ⟨t, ht, ms', hr, hp, hsp, hout, h18, fun _ _ => by rw [hmem], hk,
        hsr.regs h17 h18 hmem⟩

/-! ## `br_if` -/

theorem gen_br_if {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {n : Nat}
    {is : List Instr} {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.br_if n) = .ok (is, fin)) :
    curBase ctl + 1 ≤ σ.length ∧ σ.length - 1 < 26 ∧ fin = some σ.tail ∧ ∃ t, ctl[n]? = some t ∧
      ((t.arity = 0 ∧ ∃ f, cbField a t.target = .ok f ∧
          is = [.cbnz (regOf (σ.length - 1)) f]) ∨
        (t.arity ≠ 0 ∧ ∃ f bs, cbField a (after a (t.arity + 2)) = .ok f ∧
          branchTo t σ.tail (after a 1) = .ok bs ∧
          is = .cbz (regOf (σ.length - 1)) f :: bs)) := by
  by_cases hc : σ.length < curBase ctl + 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  cases ht : ctl[n]? with
  | none =>
      simp [genInstr, hc, ht, throw, throwThe, MonadExceptOf.throw] at hg
  | some t =>
      by_cases hlt : σ.length - 1 < 26
      · by_cases h0 : t.arity = 0
        · cases hf : cbField a t.target with
          | error e => simp [genInstr, hc, ht, opReg_ok hlt, h0, hf, bind, Except.bind] at hg
          | ok f =>
              simp [genInstr, hc, ht, opReg_ok hlt, h0, hf, bind, Except.bind, pure,
                Except.pure] at hg
              obtain ⟨rfl, rfl⟩ := hg
              exact ⟨by omega, hlt, rfl, t, rfl, .inl ⟨h0, f, hf, rfl⟩⟩
        · cases hf : cbField a (after a (t.arity + 2)) with
          | error e => simp [genInstr, hc, ht, opReg_ok hlt, h0, hf, bind, Except.bind] at hg
          | ok f =>
              cases hbt : branchTo t σ.tail (after a 1) with
              | error e =>
                  simp [genInstr, hc, ht, opReg_ok hlt, h0, hf, hbt, bind, Except.bind] at hg
              | ok bs =>
                  simp [genInstr, hc, ht, opReg_ok hlt, h0, hf, hbt, bind, Except.bind, pure,
                    Except.pure] at hg
                  obtain ⟨rfl, rfl⟩ := hg
                  exact ⟨by omega, hlt, rfl, t, rfl, .inr ⟨h0, f, bs, hf, hbt, rfl⟩⟩
      · obtain ⟨e, he⟩ := opReg_error hlt
        simp [genInstr, hc, ht, he, bind, Except.bind] at hg

theorem exec_br_if (f n : Nat) {α : Type} (m : Module) (st : Store α) (sl : Locals) :
    (∃ vs, sl.values = .i32 0 :: vs ∧
      execOne (f + 1) m st sl (.br_if n) = .Fallthrough st { sl with values := vs }) ∨
    (∃ c vs, c ≠ 0 ∧ sl.values = .i32 c :: vs ∧
      execOne (f + 1) m st sl (.br_if n) = .Break n st { sl with values := vs }) ∨
    ∃ msg, execOne (f + 1) m st sl (.br_if n) = .Invalid msg := by
  cases hv : sl.values with
  | nil => exact .inr (.inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩)
  | cons v vs =>
      cases v with
      | i32 c =>
          by_cases hc : c = 0
          · subst hc
            exact .inl ⟨vs, rfl, by simp only [execOne.eq_def, hv]⟩
          · refine .inr (.inl ⟨c, vs, hc, rfl, ?_⟩)
            simp only [execOne.eq_def, hv]
      | _ => exact .inr (.inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩)

theorem sim_br_if (F n : Nat) : InstrSim P code F (.br_if n) := by
  intro E ctl σ a is fin hgen hcode hb hctl α m st sl ms hinv hsr h64 hpc _ _ _ _
  obtain ⟨hhb, hlt, rfl, t, ht, hcase⟩ := gen_br_if hgen
  have hh := hinv.len
  have hty := hinv.types
  generalize hσl : σ.length = h at hhb hlt hcase hh hb
  cases F with
  | zero => simp only [execOne.eq_def, Outcome, or_true]
  | succ f =>
      have hbase : t.base ≤ h := Nat.le_trans (hctl.bases t (List.mem_of_getElem? ht)) hb
      have h26 := hinv.stack.1
      rcases exec_br_if f n m st sl with
        ⟨vs, hv, hex⟩ | ⟨c, vs, hc, hv, hex⟩ | ⟨msg, hex⟩
      · rw [hex]
        have hvl : vs.length = h - 1 := by rw [hv] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hv] at hst
        have hw : ms.x (regOf (h - 1)) = 0 := by
          have := hst.top; rw [hvl] at this; rw [this]; rfl
        rcases hcase with ⟨h0, g, hg, rfl⟩ | ⟨h0, g, bs, hg, hbt, rfl⟩
        · have hc0 : code ms.pc = some (encode (.cbnz (regOf (h - 1)) g)) := by
            rw [hpc]; exact (CodeAt.cons.mp hcode).1
          exact .inr ⟨_, rfl, { ms with pc := ms.pc + 4 },
            reach_exec P code hc0 (cbnz_next P hw) (.refl _), by simp [hpc, after], rfl, rfl,
            rfl, fun _ _ => rfl, Inv.pop P hinv hv _, fun _ _ => rfl, hsr.regs rfl rfl rfl⟩
        · obtain ⟨-, ha1, -, -, g2, -, hbs⟩ := gen_branchTo hbt
          have hlen : (Instr.cbz (regOf (h - 1)) g :: bs).length = t.arity + 2 := by
            rw [hbs, show t.arity = 1 by omega]; simp
          have hcz : code ms.pc = some (encode (.cbz (regOf (h - 1)) g)) := by
            rw [hpc]; exact (CodeAt.cons.mp hcode).1
          exact .inr ⟨_, rfl, _, cbz_taken P code hcz hpc hg hw, by rw [hlen], rfl, rfl,
            rfl, fun _ _ => rfl, Inv.pop P hinv hv _, fun _ _ => rfl, hsr.regs rfl rfl rfl⟩
      · rw [hex]
        have hvl : vs.length = h - 1 := by rw [hv] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hv] at hst
        have hw : ms.x (regOf (h - 1)) ≠ 0 := by
          have := hst.top; rw [hvl] at this; rw [this]
          exact fun e => hc (UInt32.toUInt64_inj.mp (by rw [e]; rfl))
        rcases hcase with ⟨h0, g, hg, rfl⟩ | ⟨h0, g, bs, hg, hbt, rfl⟩
        · have hc0 : code ms.pc = some (encode (.cbnz (regOf (h - 1)) g)) := by
            rw [hpc]; exact (CodeAt.cons.mp hcode).1
          exact break_outcome P code (sl' := { sl with values := vs }) ht hinv hsr rfl
            (cbnz_taken P code hc0 hpc hg hw) rfl
            ⟨by simp [h0], by omega, fun j hj => absurd hj (by omega),
              by rw [show t.types = [] from List.eq_nil_of_length_eq_zero h0, h0]; trivial⟩
            (fun _ _ => rfl) rfl rfl rfl rfl rfl
        · have hcz : code ms.pc = some (encode (.cbz (regOf (h - 1)) g)) := by
            rw [hpc]; exact (CodeAt.cons.mp hcode).1
          have hstep := reach_exec P code hcz (cbz_next P hw) (.refl _)
          rw [hv] at hty
          obtain ⟨ms', hr, hp, hk, hfr, h18, h17, hsp, hmem, hout⟩ :=
            run_branchTo P code (ms := { ms with pc := ms.pc + 4 }) (vs := vs) hbt
              (CodeAt.cons.mp hcode).2 (by simp [hpc, after]) (hst.pop.congr fun _ _ => rfl)
              (by rw [hvl, List.length_tail, hσl]) hty.tail
          exact break_outcome P code (sl' := { sl with values := vs }) ht hinv hsr rfl
            (hstep.trans hr) hp hk hfr h18 h17 hsp hmem hout
      · rw [hex]; exact .inr trivial

end LeanExe.A64
