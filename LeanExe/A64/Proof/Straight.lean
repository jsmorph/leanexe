import LeanExe.A64.Proof.Sim
import LeanExe.A64.Proof.Bits

/-!
The simulation of the instructions that store locals and push constants: `localSet`,
`localTee`, `constI64`, and `const`.  A store writes the frame slot of its local with `STR`,
which leaves the other slots and the memory outside the frame unchanged because slots lie 8 bytes
apart and the frame holds fewer than 512 of them.  A constant is `MOVZ` and three `MOVK`, which
build the value 16 bits at a time.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-- A step at a placed instruction that executes, followed by more steps. -/
theorem reach_exec {s t u : State} {i : Instr} (hc : code s.pc = some (encode i))
    (he : LeanExe.A64.exec P i s = some t) (hr : Reach P code t u) : Reach P code s u :=
  .next (by rw [step_at hc]; exact he) hr

/-- The instruction at index `k` of placed code. -/
theorem CodeAt.at {a : UInt64} {is : List Instr} (h : CodeAt code a is) (k : Nat)
    (hk : k < is.length) : code (after a k) = some (encode is[k]) := h k hk

/-! ## Frame slots -/

theorem toNat_slot (sp : UInt64) (i : Nat) :
    (slotAddr sp i).toNat = (sp.toNat + 8 * i) % 2 ^ 64 := by
  simp only [slotAddr, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  omega

/-- Two distinct slots of a frame of fewer than 512 lie at least 8 bytes apart. -/
theorem slot_apart {sp : UInt64} {i j : Nat} (hi : i < 512) (hj : j < 512) (hne : i ≠ j) :
    ∀ k < 8, ¬ slotAddr sp j + UInt64.ofNat k - slotAddr sp i < 8 := by
  intro k hk
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, toNat_slot sp i,
    toNat_slot sp j, UInt64.toNat_ofNat']
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  have := sp.toNat_lt
  omega

/-- A store to a slot leaves the bytes outside the frame unchanged. -/
theorem slot_inside {sp a : UInt64} {i n : Nat} (hi : i < n) (hn : n < 512)
    (h : ¬ a - sp < UInt64.ofNat (8 * n)) : ¬ a - slotAddr sp i < 8 := by
  intro hc
  apply h
  rw [UInt64.lt_iff_toNat_lt] at hc ⊢
  rw [UInt64.toNat_sub, toNat_slot sp i] at hc
  rw [UInt64.toNat_sub, UInt64.toNat_ofNat']
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this] at hc
  have := sp.toNat_lt
  have := a.toNat_lt
  omega

/-! ## The operand stack -/

/-- Popping the top of a related stack. -/
theorem StackRel.pop {s : State} {v : Value} {vs : List Value} (h : StackRel s (v :: vs)) :
    StackRel s vs := by
  refine ⟨by have := h.1; simp at this; omega, fun k hk => ?_⟩
  have := h.2 k (by simp; omega)
  simpa [List.getElem_append_left (show k < vs.reverse.length by simpa using hk)] using this

/-- The top of a related stack lies in the register of its height. -/
theorem StackRel.top {s : State} {v : Value} {vs : List Value} (h : StackRel s (v :: vs)) :
    ValRel v (s.x (regOf vs.length)) := by
  simpa using h.2 vs.length (by simp)

/-- A related stack stays related when the registers of its heights keep their values. -/
theorem StackRel.congr {s s' : State} {vs : List Value} (h : StackRel s vs)
    (hkeep : ∀ k < vs.length, s'.x (regOf k) = s.x (regOf k)) : StackRel s' vs :=
  ⟨h.1, fun k hk => by rw [hkeep k hk]; exact h.2 k hk⟩

/-! ## Stores of locals -/

/-- After `STR` of `w` into slot `i`, the locals with `v` at `i` are related, when `w` holds `v`. -/
theorem LocalsRel.store {s : State} {ls : List Value} (h : LocalsRel s ls) {i : Nat}
    (hi : i < ls.length) (hn : ls.length < 512) {v : Value} {w : UInt64} (hv : ValRel v w) :
    LocalsRel { s with mem := store64 s.mem (s.sp + UInt64.ofNat (8 * i)) w, pc := s.pc + 4 }
      (ls.set i v) := by
  intro j hj
  simp only [List.length_set] at hj
  rw [ofNat_mul8]
  by_cases hij : i = j
  · subst hij
    simp only [List.getElem_set_self]
    show ValRel v (load64 (store64 s.mem (s.sp + 8 * UInt64.ofNat i) w) (slotAddr s.sp i))
    rw [slotAddr, load64_store64_same]
    exact hv
  · rw [List.getElem_set_ne hij]
    show ValRel ls[j] (load64 (store64 s.mem (slotAddr s.sp i) w) (slotAddr s.sp j))
    rw [load64_store64_other _ _ _ _ (slot_apart (by omega) (by omega) hij)]
    exact h j hj

theorem gen_localSet {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {i : Nat}
    {is : List Instr} {fin : Option Nat}
    (hg : genInstr E ctl h a (.localSet i) = .ok (is, fin)) :
    ∃ hs : i < 4096, i < E.locals ∧ curBase ctl + 1 ≤ h ∧ h - 1 < 26 ∧
      is = [.str (regOf (h - 1)) 31 ⟨i, hs⟩] ∧ fin = some (h - 1) := by
  unfold genInstr at hg
  by_cases hc : i ≥ E.locals ∨ h < curBase ctl + 1
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h - 1 < 26
  · by_cases hs : i < 4096
    · simp [hc, opReg_ok hlt, slotOf, hs, bind, Except.bind, pure, Except.pure] at hg
      exact ⟨hs, by omega, by omega, hlt, hg.1.symm, hg.2.symm⟩
    · simp [hc, opReg_ok hlt, slotOf, hs, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind] at hg
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [hc, he, bind, Except.bind] at hg

theorem gen_localTee {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {i : Nat}
    {is : List Instr} {fin : Option Nat}
    (hg : genInstr E ctl h a (.localTee i) = .ok (is, fin)) :
    ∃ hs : i < 4096, i < E.locals ∧ curBase ctl + 1 ≤ h ∧ h - 1 < 26 ∧
      is = [.str (regOf (h - 1)) 31 ⟨i, hs⟩] ∧ fin = some h := by
  unfold genInstr at hg
  by_cases hc : i ≥ E.locals ∨ h < curBase ctl + 1
  · simp [hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h - 1 < 26
  · by_cases hs : i < 4096
    · simp [hc, opReg_ok hlt, slotOf, hs, bind, Except.bind, pure, Except.pure] at hg
      exact ⟨hs, by omega, by omega, hlt, hg.1.symm, hg.2.symm⟩
    · simp [hc, opReg_ok hlt, slotOf, hs, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind] at hg
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [hc, he, bind, Except.bind] at hg

/-- The machine's side of `STR` of the top into slot `i`. -/
theorem exec_str_slot {n : Nat} {sl : Locals} {ms : State} (hinv : Inv P n sl ms) {i : Nat}
    (hi : i < n) (hs : i < 4096) (r : Fin 32) :
    LeanExe.A64.exec P (.str r 31 ⟨i, hs⟩) ms =
      some { ms with
        mem := store64 ms.mem (ms.sp + UInt64.ofNat (8 * i)) (ms.x r), pc := ms.pc + 4 } := by
  simp only [exec, State.xsp_31, State.spAligned, mapped_slot P hinv hi, Bool.and_true,
    hinv.aligned]
  simp

theorem sim_localSet (F i : Nat) : InstrSim P code F (.localSet i) := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hs, hi, hhb, hlt, rfl, rfl⟩ := gen_localSet hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      obtain ⟨v, vs, hvs⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hv : sl.values with
        | nil => rw [hv] at hh; simp at hh; omega
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hvl : vs.length = h - 1 := by rw [hvs] at hh; simp at hh; omega
      have hil : i < (sl.params ++ sl.locals).length := by rw [hinv.count]; exact hi
      obtain ⟨s', hs', hpl, hvals⟩ := ProofKit.Locals.set?_append sl i v hil
      simp only [execOne.eq_def, hvs, hs']
      have hc : code ms.pc = some (encode (.str (regOf (h - 1)) 31 ⟨i, hs⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hstack := hinv.stack
      rw [hvs] at hstack
      refine ⟨h - 1, rfl, _, reach_exec P code hc (exec_str_slot P hinv hi hs _) (.refl _),
        ?_, rfl, rfl, ?_, ?_, ?_, fun k _ => rfl⟩
      · simp [hpc, after]
      · intro b hb'
        have hin := slot_inside hi hinv.bound hb'
        rw [slotAddr, ← ofNat_mul8] at hin
        exact store64_other _ _ _ _ hin
      · refine ⟨hstack.pop.congr (fun k _ => rfl), ?_, ?_, hinv.aligned, hinv.mapped,
          hinv.bound⟩
        · show LocalsRel _ (s'.params ++ s'.locals)
          rw [hpl]
          refine hinv.locals.store hil (by rw [hinv.count]; exact hinv.bound) ?_
          rw [← hvl]; exact hstack.top
        · show (s'.params ++ s'.locals).length = E.locals
          rw [hpl, List.length_set, hinv.count]
      · show vs.length = h - 1
        exact hvl

theorem sim_localTee (F i : Nat) : InstrSim P code F (.localTee i) := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hs, hi, hhb, hlt, rfl, rfl⟩ := gen_localTee hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      obtain ⟨v, vs, hvs⟩ : ∃ v vs, sl.values = v :: vs := by
        cases hv : sl.values with
        | nil => rw [hv] at hh; simp at hh; omega
        | cons v vs => exact ⟨v, vs, rfl⟩
      have hvl : vs.length = h - 1 := by rw [hvs] at hh; simp at hh; omega
      have hil : i < (sl.params ++ sl.locals).length := by rw [hinv.count]; exact hi
      obtain ⟨s', hs', hpl, hvals⟩ := ProofKit.Locals.set?_append sl i v hil
      simp only [execOne.eq_def, hvs, hs']
      have hc : code ms.pc = some (encode (.str (regOf (h - 1)) 31 ⟨i, hs⟩)) := by
        rw [hpc]; simpa [after_zero] using hcode 0 (by simp)
      have hstack := hinv.stack
      rw [hvs] at hstack
      refine ⟨h, rfl, _, reach_exec P code hc (exec_str_slot P hinv hi hs _) (.refl _),
        ?_, rfl, rfl, ?_, ?_, ?_, fun k _ => rfl⟩
      · simp [hpc, after]
      · intro b hb'
        have hin := slot_inside hi hinv.bound hb'
        rw [slotAddr, ← ofNat_mul8] at hin
        exact store64_other _ _ _ _ hin
      · refine ⟨?_, ?_, ?_, hinv.aligned, hinv.mapped, hinv.bound⟩
        · rw [hvals, hvs]; exact hstack.congr (fun k _ => rfl)
        · show LocalsRel _ (s'.params ++ s'.locals)
          rw [hpl]
          refine hinv.locals.store hil (by rw [hinv.count]; exact hinv.bound) ?_
          rw [← hvl]; exact hstack.top
        · show (s'.params ++ s'.locals).length = E.locals
          rw [hpl, List.length_set, hinv.count]
      · rw [hvals, hvs]; simp; omega

/-! ## Constants -/

theorem after_succ (a : UInt64) (k : Nat) : after a (k + 1) = after a k + 4 := by
  rw [← after_after]; simp [after]

theorem half_val (v : UInt64) (k : Nat) : (half v k).val = v.toNat / 65536 ^ k % 65536 := rfl

/-- The four instructions of `movImm d v` set register `d`, below 31, to `v`, and keep the
other registers, `SP`, the memory, and the UART's output. -/
theorem run_movImm {s : State} {a : UInt64} {d : Fin 32} {v : UInt64} (hd : d.val < 31)
    (hcode : CodeAt code a (movImm d v)) (hpc : s.pc = a) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 4 ∧ s'.x d = v ∧
      (∀ r, r ≠ d → s'.x r = s.x r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  have c0 := hcode 0 (by simp [movImm])
  have c1 := hcode 1 (by simp [movImm])
  have c2 := hcode 2 (by simp [movImm])
  have c3 := hcode 3 (by simp [movImm])
  simp only [movImm, List.getElem_cons_zero, List.getElem_cons_succ, after_zero] at c0 c1 c2 c3
  let w0 : UInt64 := UInt64.ofNat (half v 0).val <<< UInt64.ofNat (16 * (0 : Fin 4).val)
  let s1 : State := { s.setX d w0 with pc := s.pc + 4 }
  let w1 : UInt64 :=
    (s1.x d &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * (1 : Fin 4).val))) |||
      UInt64.ofNat (half v 1).val <<< UInt64.ofNat (16 * (1 : Fin 4).val)
  let s2 : State := { s1.setX d w1 with pc := s1.pc + 4 }
  let w2 : UInt64 :=
    (s2.x d &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * (2 : Fin 4).val))) |||
      UInt64.ofNat (half v 2).val <<< UInt64.ofNat (16 * (2 : Fin 4).val)
  let s3 : State := { s2.setX d w2 with pc := s2.pc + 4 }
  let w3 : UInt64 :=
    (s3.x d &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat (16 * (3 : Fin 4).val))) |||
      UInt64.ofNat (half v 3).val <<< UInt64.ofNat (16 * (3 : Fin 4).val)
  let s4 : State := { s3.setX d w3 with pc := s3.pc + 4 }
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  have p2 : s2.pc = after a 2 := by simp only [s2]; rw [after_succ, ← p1]
  have p3 : s3.pc = after a 3 := by simp only [s3]; rw [after_succ, ← p2]
  have p4 : s4.pc = after a 4 := by simp only [s4]; rw [after_succ, ← p3]
  have hr : Reach P code s s4 := by
    refine reach_exec P code (i := .movz d (half v 0) 0) (by rw [hpc]; exact c0) rfl ?_
    refine reach_exec P code (i := .movk d (half v 1) 1) (by rw [p1]; exact c1) rfl ?_
    refine reach_exec P code (i := .movk d (half v 2) 2) (by rw [p2]; exact c2) rfl ?_
    exact reach_exec P code (i := .movk d (half v 3) 3) (by rw [p3]; exact c3) rfl (.refl _)
  have x1 : s1.x d = w0 := State.x_setX_same (s := s) hd
  have x2 : s2.x d = w1 := State.x_setX_same (s := s1) hd
  have x3 : s3.x d = w2 := State.x_setX_same (s := s2) hd
  have x4 : s4.x d = w3 := State.x_setX_same (s := s3) hd
  have h0 : (half v 0).val < 65536 := (half v 0).isLt
  have h1 : (half v 1).val < 65536 := (half v 1).isLt
  have h2 : (half v 2).val < 65536 := (half v 2).isLt
  have h3 : (half v 3).val < 65536 := (half v 3).isLt
  have e0 : w0.toNat = (half v 0).val := by
    simp only [w0, show 16 * (0 : Fin 4).val = 0 from rfl, UInt64.toNat_shiftLeft,
      UInt64.toNat_ofNat', Nat.shiftLeft_eq]
    simp; omega
  have e1 : w1.toNat = (half v 0).val + (half v 1).val * 2 ^ 16 := by
    simp only [w1, show 16 * (1 : Fin 4).val = 16 from rfl]
    rw [movk_add _ _ 16 (by rw [x1, e0]; omega) h1 (by decide), x1, e0]
  have e2 : w2.toNat = (half v 0).val + (half v 1).val * 2 ^ 16 + (half v 2).val * 2 ^ 32 := by
    simp only [w2, show 16 * (2 : Fin 4).val = 32 from rfl]
    rw [movk_add _ _ 32 (by rw [x2, e1]; omega) h2 (by decide), x2, e1]
  have e3 : w3.toNat = v.toNat := by
    simp only [w3, show 16 * (3 : Fin 4).val = 48 from rfl]
    rw [movk_add _ _ 48 (by rw [x3, e2]; omega) h3 (by decide), x3, e2]
    simp only [half_val]
    have := v.toNat_lt
    omega
  refine ⟨s4, hr, p4, ?_, fun r hne => ?_, ?_, ?_, ?_⟩
  · rw [x4]; exact UInt64.toNat_inj.mp e3
  · show (s3.setX d w3).x r = s.x r
    rw [State.x_setX_ne (Ne.symm hne)]
    show (s2.setX d w2).x r = s.x r
    rw [State.x_setX_ne (Ne.symm hne)]
    show (s1.setX d w1).x r = s.x r
    rw [State.x_setX_ne (Ne.symm hne)]
    show (s.setX d w0).x r = s.x r
    rw [State.x_setX_ne (Ne.symm hne)]
  · simp [s4, s3, s2, s1]
  · simp [s4, s3, s2, s1]
  · simp [s4, s3, s2, s1]

theorem gen_const {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    {fin : Option Nat} {inst : Instruction} {w : UInt64}
    (hinst : inst = .constI64 w ∨ ∃ c : UInt32, inst = .const c ∧ w = c.toUInt64)
    (hg : genInstr E ctl h a inst = .ok (is, fin)) :
    h < 26 ∧ is = movImm (regOf h) w ∧ fin = some (h + 1) := by
  by_cases hlt : h < 26
  · rcases hinst with rfl | ⟨c, rfl, rfl⟩ <;>
      simp [genInstr, opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg <;>
      exact ⟨hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    rcases hinst with rfl | ⟨c, rfl, rfl⟩ <;> simp [genInstr, he, bind, Except.bind] at hg

/-- The simulation of a constant `v` that `w`, its register word, holds. -/
theorem sim_const_of {F : Nat} {inst : Instruction} {w : UInt64} {v : Value}
    (hinst : inst = .constI64 w ∨ ∃ c : UInt32, inst = .const c ∧ w = c.toUInt64)
    (hv : ValRel v w)
    (hexec : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      execOne (f + 1) m st sl inst = .Fallthrough st { sl with values := v :: sl.values }) :
    InstrSim P code F inst := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hlt, rfl, rfl⟩ := gen_const hinst hgen
  cases F with
  | zero => rcases hinst with rfl | ⟨c, rfl, rfl⟩ <;> simp only [execOne.eq_def, Outcome]
  | succ f =>
      rw [hexec f m st sl]
      obtain ⟨s', hr, hp, hx, hkeep, hsp, hmem, hout⟩ :=
        run_movImm P code (regOf_lt_31 h hlt) hcode hpc
      refine ⟨h + 1, rfl, s', hr, by simpa [movImm] using hp, hsp, hout, ?_, ?_, ?_, ?_⟩
      · intro b _; rw [hmem]
      · refine ⟨StackRel.push hinv.stack (by omega) ?_ ?_, hinv.locals.congr hmem hsp,
          hinv.count, by rw [hsp]; exact hinv.aligned, by rw [hsp]; exact hinv.mapped,
          hinv.bound⟩
        · rw [hh, hx]; exact hv
        · intro k hk
          exact hkeep _ (fun e => absurd (regOf_inj k (by omega) h hlt e) (by omega))
      · simp [hh]
      · intro k hk
        exact hkeep _ (fun e => absurd (regOf_inj k (by omega) h hlt e) (by omega))

theorem sim_constI64 (F : Nat) (w : UInt64) : InstrSim P code F (.constI64 w) :=
  sim_const_of P code (v := .i64 w) (.inl rfl) rfl (fun _ _ _ _ _ => by simp only [execOne.eq_def])

theorem sim_const (F : Nat) (c : UInt32) : InstrSim P code F (.const c) :=
  sim_const_of P code (w := c.toUInt64) (v := .i32 c) (.inr ⟨c, rfl, rfl⟩) rfl
    (fun _ _ _ _ _ => by simp only [execOne.eq_def])

/-! ## Comparisons -/

theorem sub_eq_zero_iff' (x y : UInt64) : x - y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· + y) h
    simpa using this
  · intro h; subst h; simp

/-- `SUBS XZR` of `x` and `y`, which `he` executes, followed by `CSINC r, XZR, XZR, NE`, sets
register `r`, below 31, to 1 when `x = y` and to 0 otherwise. -/
theorem run_cset {s : State} {a : UInt64} {i0 : Instr} {r : Fin 32} {x y : UInt64}
    (hr : r.val < 31) (hc0 : code a = some (encode i0))
    (hc1 : code (after a 1) = some (encode (.csinc r 31 31 1))) (hpc : s.pc = a)
    (he : LeanExe.A64.exec P i0 s = some { s.subs 31 x y with pc := s.pc + 4 }) :
    ∃ s', Reach P code s s' ∧ s'.pc = after a 2 ∧ s'.x r = (if x = y then 1 else 0) ∧
      (∀ q, q ≠ r → s'.x q = s.x q) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.out = s.out := by
  let s1 : State := { s.subs 31 x y with pc := s.pc + 4 }
  have hx1 : ∀ q, s1.x q = s.x q := by
    intro q
    show (s.setX 31 (x - y)).x q = s.x q
    unfold State.setX; rw [ite_eq_right (by decide)]
  have hz : s1.zFlag = (x - y == 0) := rfl
  have p1 : s1.pc = after a 1 := by simp [s1, hpc, after]
  refine ⟨{ s1.setX r (if s1.condHolds 1 then s1.x 31 else s1.x 31 + 1) with pc := s1.pc + 4 },
    reach_exec P code (by rw [hpc]; exact hc0) he
      (reach_exec P code (by rw [p1]; exact hc1) rfl (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show s1.pc + 4 = after a 2
    rw [p1]; exact (after_succ a 1).symm
  · rw [State.x_withPc, State.x_setX_same hr]
    have h31 : s1.x 31 = 0 := by unfold State.x; rw [dite_eq_right (by decide)]
    have hc : s1.condHolds 1 = !(x - y == 0) := by
      unfold State.condHolds; rw [hz]; rfl
    rw [h31, hc]
    by_cases hxy : x = y
    · subst hxy; simp
    · have : ¬ x - y = 0 := fun e => hxy ((sub_eq_zero_iff' x y).mp e)
      simp [hxy, this]
  · intro q hq
    rw [State.x_withPc, State.x_setX_ne (Ne.symm hq), hx1]
  · show (s1.setX r _).sp = s.sp
    rw [State.setX_sp]; exact State.setX_sp
  · show (s1.setX r _).mem = s.mem
    rw [State.setX_mem]; exact State.setX_mem
  · show (s1.setX r _).out = s.out
    rw [State.setX_out]; exact State.setX_out

theorem gen_cmp {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    {fin : Option Nat} {inst : Instruction} (hinst : inst = .eqI64 ∨ inst = .eq)
    (hg : genInstr E ctl h a inst = .ok (is, fin)) :
    curBase ctl + 2 ≤ h ∧ h - 1 < 26 ∧
      is = [.subsReg 31 (regOf (h - 2)) (regOf (h - 1)), .csinc (regOf (h - 2)) 31 31 1] ∧
      fin = some (h - 1) := by
  by_cases hc : h < curBase ctl + 2
  · rcases hinst with rfl | rfl <;>
      simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h - 1 < 26
  · rcases hinst with rfl | rfl <;>
      simp [genInstr, hc, opReg_ok hlt, opReg_ok (show h - 2 < 26 by omega), bind, Except.bind,
        pure, Except.pure] at hg <;>
      exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    by_cases hlt2 : h - 2 < 26
    · rcases hinst with rfl | rfl <;>
        simp [genInstr, hc, he, opReg_ok hlt2, bind, Except.bind] at hg
    · obtain ⟨e2, he2⟩ := opReg_error hlt2
      rcases hinst with rfl | rfl <;> simp [genInstr, hc, he2, bind, Except.bind] at hg

theorem gen_eqz {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    {fin : Option Nat} {inst : Instruction} (hinst : inst = .eqzI64 ∨ inst = .eqz)
    (hg : genInstr E ctl h a inst = .ok (is, fin)) :
    curBase ctl + 1 ≤ h ∧ h - 1 < 26 ∧
      is = [.subsImm 31 (regOf (h - 1)) 0, .csinc (regOf (h - 1)) 31 31 1] ∧ fin = some h := by
  by_cases hc : h < curBase ctl + 1
  · rcases hinst with rfl | rfl <;>
      simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  by_cases hlt : h - 1 < 26
  · rcases hinst with rfl | rfl <;>
      simp [genInstr, hc, opReg_ok hlt, bind, Except.bind, pure, Except.pure] at hg <;>
      exact ⟨by omega, hlt, hg.1.symm, hg.2.symm⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    rcases hinst with rfl | rfl <;> simp [genInstr, hc, he, bind, Except.bind] at hg

/-- The outcome of a comparison whose result `c` replaces the operands above `vs` and lies,
zero-extended, in the register of height `vs.length`. -/
theorem cmp_outcome {E : Env} {ctl : List Ctl} {a : UInt64} {α : Type} {st : Store α}
    {sl : Locals} {ms ms' : State} {vs : List Value} (c : UInt32)
    (hinv : Inv P E.locals sl ms) (hb : curBase ctl ≤ vs.length)
    (hlt : vs.length < 26) (hstack : StackRel ms vs) (hr : Reach P code ms ms')
    (hpc : ms'.pc = after a 2) (hx : ms'.x (regOf vs.length) = c.toUInt64)
    (hkeep : ∀ q, q ≠ regOf vs.length → ms'.x q = ms.x q) (hsp : ms'.sp = ms.sp)
    (hmem : ms'.mem = ms.mem) (hout : ms'.out = ms.out) :
    Outcome P code E ctl (some (vs.length + 1)) (after a 2)
      (.Fallthrough st { sl with values := .i32 c :: vs }) ms := by
  have hk : ∀ j < vs.length, ms'.x (regOf j) = ms.x (regOf j) := fun j hj =>
    hkeep _ (fun e => absurd (regOf_inj j (by omega) vs.length hlt e) (by omega))
  refine ⟨vs.length + 1, rfl, ms', hr, hpc, hsp, hout, fun b _ => by rw [hmem], ?_, by simp,
    fun j hj => hk j (by omega)⟩
  refine ⟨StackRel.push hstack hlt (by rw [hx]; rfl) hk, hinv.locals.congr hmem hsp, hinv.count,
    by rw [hsp]; exact hinv.aligned, by rw [hsp]; exact hinv.mapped, hinv.bound⟩

theorem cset_val (x y : UInt64) (c : Prop) [Decidable c] (hc : x = y ↔ c) :
    (if x = y then (1 : UInt64) else 0) = (if c then (1 : UInt32) else 0).toUInt64 := by
  by_cases h : c
  · rw [ite_eq_left (hc.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun e => h (hc.mp e)), ite_eq_right h]; rfl

theorem sim_eqI64 (F : Nat) : InstrSim P code F .eqI64 := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hhb, hlt, rfl, rfl⟩ := gen_cmp (.inl rfl) hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      simp only [execOne.eq_def]
      split
      next y x vs hvs =>
        have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hy : ms.x (regOf (h - 1)) = y := by
          have := hst.top; rw [show (Value.i64 x :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = x := by
          have := hst.pop.top; rw [hvl] at this; exact this
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_cset P code (regOf_lt_31 (h - 2) (by omega))
            (by simpa [after_zero] using hcode 0 (by simp))
            (by simpa using hcode 1 (by simp)) hpc rfl
        rw [show h - 1 = vs.length + 1 by omega]
        apply cmp_outcome P code _ hinv (vs := vs) (by omega) (by omega)
          hst.pop.pop hr hp _ _ hsp hmem hout
        · rw [hvl, hres, hx, hy]; exact cset_val x y (x = y) Iff.rfl
        · rw [hvl]; exact hkeep
      next => trivial

theorem sim_eq (F : Nat) : InstrSim P code F .eq := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hhb, hlt, rfl, rfl⟩ := gen_cmp (.inr rfl) hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      simp only [execOne.eq_def]
      split
      next y x vs hvs =>
        have hvl : vs.length = h - 2 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hy : ms.x (regOf (h - 1)) = y.toUInt64 := by
          have := hst.top; rw [show (Value.i32 x :: vs).length = h - 1 by simp; omega] at this
          exact this
        have hx : ms.x (regOf (h - 2)) = x.toUInt64 := by
          have := hst.pop.top; rw [hvl] at this; exact this
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_cset P code (regOf_lt_31 (h - 2) (by omega))
            (by simpa [after_zero] using hcode 0 (by simp))
            (by simpa using hcode 1 (by simp)) hpc rfl
        rw [show h - 1 = vs.length + 1 by omega]
        apply cmp_outcome P code _ hinv (vs := vs) (by omega) (by omega)
          hst.pop.pop hr hp _ _ hsp hmem hout
        · rw [hvl, hres, hx, hy]
          exact cset_val _ _ (x = y) ⟨fun e => UInt32.toUInt64_inj.mp e, fun e => by rw [e]⟩
        · rw [hvl]; exact hkeep
      next => trivial

theorem State.xsp_eq_x {s : State} {r : Fin 32} (h : r.val < 31) : s.xsp r = s.x r := by
  simp [State.xsp, State.x, h]

theorem sim_eqz_of {F : Nat} {inst : Instruction} (hinst : inst = .eqzI64 ∨ inst = .eqz)
    (hcase : ∀ f {α : Type} (m : Module) (st : Store α) (sl : Locals),
      (∃ v vs w, sl.values = v :: vs ∧ ValRel v w ∧
        execOne (f + 1) m st sl inst =
          .Fallthrough st { sl with values := .i32 (if w = 0 then 1 else 0) :: vs }) ∨
      ∃ msg, execOne (f + 1) m st sl inst = .Invalid msg) :
    InstrSim P code F inst := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hhb, hlt, rfl, rfl⟩ := gen_eqz hinst hgen
  cases F with
  | zero => rcases hinst with rfl | rfl <;> simp only [execOne.eq_def, Outcome]
  | succ f =>
      rcases hcase f m st sl with ⟨v, vs, w, hvs, hvw, hex⟩ | ⟨msg, hex⟩
      · rw [hex]
        have hvl : vs.length = h - 1 := by rw [hvs] at hh; simp at hh; omega
        have hst := hinv.stack
        rw [hvs] at hst
        have hw : ms.x (regOf (h - 1)) = w := by
          have := hst.top; rw [hvl] at this
          cases v <;> simp only [ValRel] at hvw this <;>
            first | (rw [this, hvw]) | exact absurd hvw id
        obtain ⟨ms', hr, hp, hres, hkeep, hsp, hmem, hout⟩ :=
          run_cset P code (x := ms.x (regOf (h - 1))) (y := 0) (regOf_lt_31 (h - 1) hlt)
            (by simpa [after_zero] using hcode 0 (by simp))
            (by simpa using hcode 1 (by simp)) hpc
            (by simp only [exec, State.xsp_eq_x (regOf_lt_31 (h - 1) hlt)]; rfl)
        rw [show h = vs.length + 1 by omega]
        apply cmp_outcome P code _ hinv (vs := vs) (by omega) (by omega) hst.pop hr hp _ _ hsp
          hmem hout
        · rw [hvl, hres, hw]; exact cset_val w 0 (w = 0) Iff.rfl
        · rw [hvl]; exact hkeep
      · rw [hex]; trivial

theorem sim_eqzI64 (F : Nat) : InstrSim P code F .eqzI64 :=
  sim_eqz_of P code (.inl rfl) fun f α m st sl => by
    cases hv : sl.values with
    | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
    | cons v vs =>
        cases v with
        | i64 x => exact .inl ⟨.i64 x, vs, x, rfl, rfl, by simp only [execOne.eq_def, hv]⟩
        | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩

theorem sim_eqz (F : Nat) : InstrSim P code F .eqz :=
  sim_eqz_of P code (.inr rfl) fun f α m st sl => by
    cases hv : sl.values with
    | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
    | cons v vs =>
        cases v with
        | i32 x =>
            refine .inl ⟨.i32 x, vs, x.toUInt64, rfl, rfl, ?_⟩
            simp only [execOne.eq_def, hv]
            congr 3
            by_cases h : x = 0
            · subst h; rfl
            · have : x.toUInt64 ≠ 0 := fun e => h (UInt32.toUInt64_inj.mp (by rw [e]; rfl))
              rw [ite_eq_right h, ite_eq_right this]
        | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩

theorem gen_extend {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    {fin : Option Nat} (hg : genInstr E ctl h a .extendUI32 = .ok (is, fin)) :
    curBase ctl + 1 ≤ h ∧ is = [] ∧ fin = some h := by
  by_cases hc : h < curBase ctl + 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  · simp [genInstr, hc, pure, Except.pure] at hg
    exact ⟨by omega, by cases hg.1; rfl, by cases hg.2; rfl⟩

theorem sim_extendUI32 (F : Nat) : InstrSim P code F .extendUI32 := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc
  obtain ⟨hhb, rfl, rfl⟩ := gen_extend hgen
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      simp only [execOne.eq_def]
      split
      next x vs hvs =>
        have hst := hinv.stack
        rw [hvs] at hst
        refine ⟨h, rfl, ms, .refl _, by simp [hpc, after_zero], rfl, rfl, fun _ _ => rfl, ?_,
          by rw [← hh, hvs]; simp, fun _ _ => rfl⟩
        refine ⟨⟨by have := hst.1; simpa using this, fun k hk => ?_⟩, hinv.locals, hinv.count,
          hinv.aligned, hinv.mapped, hinv.bound⟩
        have := hst.2 k (by simpa using hk)
        by_cases hkl : k < vs.length
        · simpa [List.getElem_append_left (show k < vs.reverse.length by simpa using hkl)]
            using this
        · have : k = vs.length := by simp at hk; omega
          subst this
          have htop : ms.x (regOf vs.length) = x.toUInt64 := hst.top
          simp only [List.reverse_cons, List.getElem_append, List.length_reverse, Nat.lt_irrefl,
            dite_false, Nat.sub_self, List.getElem_cons_zero, ValRel]
          rw [htop]
          apply UInt64.toNat_inj.mp
          simp only [UInt32.toNat_toUInt64, UInt64.toNat_ofNat']
          have := x.toNat_lt
          omega
      next => trivial

end LeanExe.A64
