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

end LeanExe.A64
