import LeanExe.A64.Proof.Control
import LeanExe.A64.Proof.Call
import LeanExe.ProofKit.Exec
import Interpreter.Wasm.Semantics.Lemmas

/-!
The simulation of instruction lists and of the constructs `block`, `loop`, and `if`.  The
generator places a construct's end, which a branch to a block or an `if` targets, at the address
that the size functions `instrSize` and `listSize` compute before it generates the body, so the
proofs rest on the lemma that the generated code has the length that those functions compute.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## The generator's constructs and lists -/

theorem any_ne {o : Option Nat} {n : Nat}
    (h : ¬ Option.any (fun x => !decide (x = n)) o = true) : ∀ x, o = some x → x = n := by
  intro x hx
  subst hx
  simpa using h

theorem gen_block {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {pa ra : Nat}
    {body : List Instruction} {pts rts : List ValueType} {is : List Instr} {fin : Option Nat}
    (hg : genInstr E ctl h a (.block pa ra body pts rts) = .ok (is, fin)) :
    let n := (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) h body).1
    pa = 0 ∧ ra ≤ 1 ∧ fin = some (h + ra) ∧ ∃ fb,
      genList E ({ target := after a n, arity := ra, base := h } :: ctl) h a body = .ok (is, fb) ∧
        ∀ x, fb = some x → x = h + ra := by
  intro n
  by_cases hc : pa ≠ 0 ∨ ra > 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hpa : pa = 0 := by omega
  have hra : ¬ ra > 1 := by omega
  subst hpa
  simp [genInstr, hra, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hg
  split at hg
  · cases hg
  rename_i v hl
  split at hg
  · cases hg
  rename_i hend
  cases hg
  exact ⟨rfl, by omega, rfl, v.2, hl, any_ne hend⟩

theorem gen_loop {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {pa ra : Nat}
    {body : List Instruction} {pts rts : List ValueType} {is : List Instr} {fin : Option Nat}
    (hg : genInstr E ctl h a (.loop pa ra body pts rts) = .ok (is, fin)) :
    pa = 0 ∧ ra ≤ 1 ∧ fin = some (h + ra) ∧ ∃ fb,
      genList E ({ target := a, arity := 0, base := h } :: ctl) h a body = .ok (is, fb) ∧
        ∀ x, fb = some x → x = h + ra := by
  by_cases hc : pa ≠ 0 ∨ ra > 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hpa : pa = 0 := by omega
  have hra : ¬ ra > 1 := by omega
  subst hpa
  simp [genInstr, hra, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hg
  split at hg
  · cases hg
  rename_i v hl
  split at hg
  · cases hg
  rename_i hend
  cases hg
  exact ⟨rfl, by omega, rfl, v.2, hl, any_ne hend⟩

theorem gen_iff {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {pa ra : Nat}
    {thn els : List Instruction} {pts rts : List ValueType} {is : List Instr} {fin : Option Nat}
    (hg : genInstr E ctl h a (.iff pa ra thn els pts rts) = .ok (is, fin)) :
    let ar := ra :: ctl.map (·.arity)
    let aB := after a (1 + (listSize (sigOf E.callee) ar (h - 1) thn).1)
    let aEnd := after (after aB 1) (listSize (sigOf E.callee) ar (h - 1) els).1
    let inner : List Ctl := { target := aEnd, arity := ra, base := h - 1 } :: ctl
    pa = 0 ∧ ra ≤ 1 ∧ curBase ctl + 1 ≤ h ∧ h - 1 < 26 ∧ fin = some (h - 1 + ra) ∧
      ∃ ti ta ei ea f g, genList E inner (h - 1) (after a 1) thn = .ok (ti, ta) ∧
        genList E inner (h - 1) (after aB 1) els = .ok (ei, ea) ∧
        (∀ x, ta = some x → x = h - 1 + ra) ∧ (∀ x, ea = some x → x = h - 1 + ra) ∧
        cbField a (after aB 1) = .ok f ∧ bField aB aEnd = .ok g ∧
        is = .cbz (regOf (h - 1)) f :: (ti ++ .b g :: ei) := by
  intro ar aB aEnd inner
  by_cases hc : pa ≠ 0 ∨ ra > 1 ∨ h < curBase ctl + 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hpa : pa = 0 := by omega
  have hra : ¬ ra > 1 := by omega
  have hh : ¬ h < curBase ctl + 1 := by omega
  subst hpa
  by_cases hlt : h - 1 < 26
  · simp [genInstr, hra, hh, opReg_ok hlt, bind, Except.bind, pure, Except.pure, throw,
      throwThe, MonadExceptOf.throw] at hg
    split at hg
    · cases hg
    rename_i v hthn
    split at hg
    · cases hg
    rename_i v1 hels
    split at hg
    · cases hg
    rename_i hends
    split at hg
    · cases hg
    rename_i f hf
    split at hg
    · cases hg
    rename_i g hb
    cases hg
    exact ⟨rfl, by omega, by omega, hlt, rfl, v.1, v.2, v1.1, v1.2, f, g, hthn, hels,
      any_ne (not_or.mp hends).1, any_ne (not_or.mp hends).2, hf, hb, rfl⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [genInstr, hra, hh, he, bind, Except.bind] at hg

theorem gen_nil {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    {fin : Option Nat} (hg : genList E ctl h a [] = .ok (is, fin)) : is = [] ∧ fin = some h := by
  simp [genList, pure, Except.pure] at hg
  simp [hg]

theorem gen_cons {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {i : Instruction}
    {rest : List Instruction} {is : List Instr} {fin : Option Nat}
    (hg : genList E ctl h a (i :: rest) = .ok (is, fin)) :
    ∃ c1 f1, genInstr E ctl h a i = .ok (c1, f1) ∧
      ((f1 = none ∧ is = c1 ∧ fin = none) ∨
        ∃ h' c2, f1 = some h' ∧ genList E ctl h' (after a c1.length) rest = .ok (c2, fin) ∧
          is = c1 ++ c2) := by
  cases h1 : genInstr E ctl h a i with
  | error e => simp [genList, h1, bind, Except.bind] at hg
  | ok r =>
      obtain ⟨c1, f1⟩ := r
      refine ⟨c1, f1, rfl, ?_⟩
      cases f1 with
      | none =>
          simp [genList, h1, bind, Except.bind, pure, Except.pure] at hg
          exact .inl ⟨rfl, hg.1.symm, hg.2.symm⟩
      | some h' =>
          cases h2 : genList E ctl h' (after a c1.length) rest with
          | error e => simp [genList, h1, h2, bind, Except.bind] at hg
          | ok r2 =>
              obtain ⟨c2, f2⟩ := r2
              simp [genList, h1, h2, bind, Except.bind, pure, Except.pure] at hg
              obtain ⟨rfl, rfl⟩ := hg
              exact .inr ⟨h', c2, rfl, h2, rfl⟩

theorem branchTo_length {t : Ctl} {h : Nat} {a : UInt64} {is : List Instr}
    (hg : branchTo t h a = .ok is) : is.length = t.arity + 1 := by
  obtain ⟨-, ha1, -, f, -, rfl⟩ := gen_branchTo hg
  by_cases h1 : t.arity = 1
  · simp [h1]
  · simp [h1]; omega

/-! ## Sizes -/

/-- The generated code of an instruction has the length that `instrSize` computes, and its end
is reachable when `instrSize` says so, given that the generated code of each instruction list
smaller than the instruction has the length that `listSize` computes. -/
theorem genInstr_size_of {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {inst : Instruction}
    {is : List Instr} {fin : Option Nat}
    (ih : ∀ (ctl : List Ctl) (h : Nat) (a : UInt64) (p : List Instruction) (is : List Instr)
      (fin : Option Nat), sizeOf p < sizeOf inst → genList E ctl h a p = .ok (is, fin) →
      is.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) h p).1)
    (hg : genInstr E ctl h a inst = .ok (is, fin)) :
    is.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) h inst).1 ∧
      fin = (instrSize (sigOf E.callee) (ctl.map (·.arity)) h inst).2 := by
  cases inst with
  | localGet i => obtain ⟨_, _, _, rfl, rfl⟩ := gen_localGet hg; simp [instrSize]
  | localSet i => obtain ⟨_, _, _, _, rfl, rfl⟩ := gen_localSet hg; simp [instrSize]
  | localTee i => obtain ⟨_, _, _, _, rfl, rfl⟩ := gen_localTee hg; simp [instrSize]
  | constI64 w => obtain ⟨_, rfl, rfl⟩ := gen_const (.inl rfl) hg; simp [instrSize, movImm]
  | const c =>
      obtain ⟨_, rfl, rfl⟩ := gen_const (.inr ⟨c, rfl, rfl⟩) hg; simp [instrSize, movImm]
  | eqI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_cmp (.inl rfl) hg; simp [instrSize]
  | eq => obtain ⟨_, _, rfl, rfl⟩ := gen_cmp (.inr rfl) hg; simp [instrSize]
  | eqzI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_eqz (.inl rfl) hg; simp [instrSize]
  | eqz => obtain ⟨_, _, rfl, rfl⟩ := gen_eqz (.inr rfl) hg; simp [instrSize]
  | neI64 | ltUI64 | leUI64 | geUI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genCmp_ok hg
      simp [instrSize]
  | addI64 | subI64 | mulI64 | andI64 | and | orI64 | xorI64 | shlI64 | shrUI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genBin_ok hg
      simp [instrSize]
  | wrapI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_wrap hg; simp [instrSize]
  | extendUI32 => obtain ⟨_, rfl, rfl⟩ := gen_extend hg; simp [instrSize]
  | remUI64 =>
      obtain ⟨_, _, _, _, rfl, rfl⟩ := gen_divrem (.inl ⟨rfl, rfl⟩) hg; simp [instrSize]
  | divUI64 =>
      obtain ⟨_, _, _, _, rfl, rfl⟩ := gen_divrem (.inr ⟨rfl, rfl⟩) hg; simp [instrSize]
  | unreachable => obtain ⟨_, _, rfl, rfl⟩ := gen_unreachable hg; simp [instrSize]
  | br n =>
      obtain ⟨t, ht, hb, rfl⟩ := gen_br hg
      simp [instrSize, ht, branchTo_length hb]
  | br_if n =>
      obtain ⟨-, -, rfl, t, ht, ⟨h0, f, -, rfl⟩ | ⟨h0, f, bs, -, hb, rfl⟩⟩ :=
        gen_br_if hg
      · simp [instrSize, ht, h0]
      · simp [instrSize, ht, h0, branchTo_length hb]
  | ret =>
      obtain ⟨t, ht, hb, rfl⟩ := gen_ret hg
      simp [instrSize, ht, branchTo_length hb]
  | block pa ra body pts rts =>
      obtain ⟨-, -, rfl, fb, hl, -⟩ := gen_block hg
      have hs := ih _ h a body is fb (by simp; omega) hl
      simp only [List.map_cons] at hs
      constructor
      · simp only [instrSize]
        exact hs
      · simp only [instrSize]
  | loop pa ra body pts rts =>
      obtain ⟨-, -, rfl, fb, hl, -⟩ := gen_loop hg
      have hs := ih _ h a body is fb (by simp; omega) hl
      simp only [List.map_cons] at hs
      constructor
      · simp only [instrSize]
        exact hs
      · simp only [instrSize]
  | call k =>
      obtain ⟨target, p, r, hk, -, -, -, hr1, -, -, spills, moves, reloads, g, rfl, hs, -, hm, -,
        hrl, -, -, rfl⟩ := gen_call hg
      simp only [instrSize, sigOf, hk, Option.map_some, List.length_append, List.length_cons,
        List.length_nil, hs, hm, hrl]
      refine ⟨?_, trivial⟩
      split <;> simp <;> omega
  | iff pa ra thn els pts rts =>
      obtain ⟨-, -, -, -, rfl, ti, ta, ei, ea, f, g, ht, he, -, -, -, -, rfl⟩ := gen_iff hg
      have hst := ih _ _ _ thn ti ta (by simp; omega) ht
      have hse := ih _ _ _ els ei ea (by simp; omega) he
      simp only [List.map_cons] at hst hse
      constructor
      · simp only [instrSize, List.length_cons, List.length_append]
        omega
      · simp only [instrSize]
  | _ => simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hg

mutual

/-- The generated code of an instruction has the length that `instrSize` computes, and its end
is reachable when `instrSize` says so. -/
theorem genInstr_size {E : Env} : (ctl : List Ctl) → (h : Nat) → (a : UInt64) →
    (inst : Instruction) → (is : List Instr) → (fin : Option Nat) →
    genInstr E ctl h a inst = .ok (is, fin) →
    is.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) h inst).1 ∧
      fin = (instrSize (sigOf E.callee) (ctl.map (·.arity)) h inst).2
  | _, _, _, _, _, _, hg =>
      genInstr_size_of (fun ctl h a p is fin _ hl => (genList_size ctl h a p is fin hl).1) hg
termination_by _ _ _ inst _ _ _ => sizeOf inst
decreasing_by all_goals (try simp_wf); all_goals omega

/-- The generated code of an instruction list has the length that `listSize` computes, and its
end is reachable when `listSize` says so. -/
theorem genList_size {E : Env} : (ctl : List Ctl) → (h : Nat) → (a : UInt64) →
    (p : List Instruction) → (is : List Instr) → (fin : Option Nat) →
    genList E ctl h a p = .ok (is, fin) →
    is.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) h p).1 ∧
      fin = (listSize (sigOf E.callee) (ctl.map (·.arity)) h p).2
  | ctl, h, a, [], is, fin, hg => by
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      simp [listSize]
  | ctl, h, a, i :: rest, is, fin, hg => by
      obtain ⟨c1, f1, h1, ⟨hf1, his, hfin⟩ | ⟨h', c2, hf1, h2, his⟩⟩ := gen_cons hg
      · subst hf1 his hfin
        have s1 := genInstr_size ctl h a i _ _ h1
        constructor
        · simp only [listSize, ← s1.2]
          exact s1.1
        · simp only [listSize, ← s1.2]
      · subst hf1 his
        have s1 := genInstr_size ctl h a i _ _ h1
        have s2 := genList_size ctl h' (after a c1.length) rest c2 fin h2
        constructor
        · simp only [listSize, ← s1.2, List.length_append, s1.1, s2.1]
        · simp only [listSize, ← s1.2, s2.2]
termination_by _ _ _ p _ _ _ => sizeOf p
decreasing_by all_goals (try simp_wf); all_goals omega

end

/-! ## Composition -/

theorem genInstr_base {E : Env} {ctl : List Ctl} {h : Nat} {a : UInt64} {inst : Instruction}
    {is : List Instr} {h' : Nat} (hg : genInstr E ctl h a inst = .ok (is, some h'))
    (hb : curBase ctl ≤ h) : curBase ctl ≤ h' := by
  cases inst with
  | localGet i => obtain ⟨_, _, _, _, he⟩ := gen_localGet hg; cases he; omega
  | localSet i => obtain ⟨_, _, _, _, _, he⟩ := gen_localSet hg; cases he; omega
  | localTee i => obtain ⟨_, _, _, _, _, he⟩ := gen_localTee hg; cases he; omega
  | constI64 w => obtain ⟨_, _, he⟩ := gen_const (.inl rfl) hg; cases he; omega
  | const c => obtain ⟨_, _, he⟩ := gen_const (.inr ⟨c, rfl, rfl⟩) hg; cases he; omega
  | eqI64 => obtain ⟨_, _, _, he⟩ := gen_cmp (.inl rfl) hg; cases he; omega
  | eq => obtain ⟨_, _, _, he⟩ := gen_cmp (.inr rfl) hg; cases he; omega
  | eqzI64 => obtain ⟨_, _, _, he⟩ := gen_eqz (.inl rfl) hg; cases he; omega
  | eqz => obtain ⟨_, _, _, he⟩ := gen_eqz (.inr rfl) hg; cases he; omega
  | neI64 | ltUI64 | leUI64 | geUI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, _, he⟩ := genCmp_ok hg
      cases he
      omega
  | addI64 | subI64 | mulI64 | andI64 | and | orI64 | xorI64 | shlI64 | shrUI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, _, he⟩ := genBin_ok hg
      cases he
      omega
  | wrapI64 => obtain ⟨_, _, _, he⟩ := gen_wrap hg; cases he; omega
  | extendUI32 => obtain ⟨_, _, he⟩ := gen_extend hg; cases he; omega
  | remUI64 =>
      obtain ⟨_, _, _, _, _, he⟩ := gen_divrem (.inl ⟨rfl, rfl⟩) hg; cases he; omega
  | divUI64 =>
      obtain ⟨_, _, _, _, _, he⟩ := gen_divrem (.inr ⟨rfl, rfl⟩) hg; cases he; omega
  | unreachable => obtain ⟨_, _, _, he⟩ := gen_unreachable hg; cases he
  | br n => obtain ⟨_, _, _, he⟩ := gen_br hg; cases he
  | br_if n => obtain ⟨_, _, he, _⟩ := gen_br_if hg; cases he; omega
  | ret => obtain ⟨_, _, _, he⟩ := gen_ret hg; cases he
  | block pa ra body pts rts => obtain ⟨_, _, he, _⟩ := gen_block hg; cases he; omega
  | loop pa ra body pts rts => obtain ⟨_, _, he, _⟩ := gen_loop hg; cases he; omega
  | iff pa ra thn els pts rts => obtain ⟨_, _, _, _, he, _⟩ := gen_iff hg; cases he; omega
  | call k =>
      obtain ⟨_, _, _, _, hpb, -, -, -, -, -, _, _, _, _, -, -, -, -, -, -, -, -, he⟩ := gen_call hg
      cases he
      omega
  | _ => simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hg

/-- An outcome from a state that the machine reaches from `ms` with SP, X18, the UART's output,
the memory outside the frame, and the registers below the innermost base unchanged, as an outcome
from `ms`. -/
theorem Outcome.trans {E : Env} {ctl : List Ctl} {fin : Option Nat} {endA : UInt64} {α : Type}
    {r : Continuation α} {ms ms1 : State} (hctl : CtlOk ctl) (hr : Reach P code ms ms1)
    (hsp : ms1.sp = ms.sp) (hout : ms1.out = ms.out) (h18 : ms1.x 18 = ms.x 18)
    (hmf : MemFrame (ms.x 18) ms.sp (E.locals + spillSlots) ms ms1)
    (hfr : Frame (curBase ctl) ms ms1) (ho : Outcome P code E ctl fin endA r ms1) :
    Outcome P code E ctl fin endA r ms := by
  have hmf2 : ∀ ms' : State, MemFrame (ms1.x 18) ms1.sp (E.locals + spillSlots) ms1 ms' →
      MemFrame (ms.x 18) ms.sp (E.locals + spillSlots) ms ms' :=
    fun ms' h b hb => by rw [h b (by rwa [hsp, h18]), hmf b hb]
  rcases ho with ⟨hc, ms', hr', hp, hout'⟩ | ho
  · exact .inl ⟨hc, ms', hr.trans hr', hp, by rw [hout', hout]⟩
  refine .inr ?_
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨h', hf, ms', hr', hp, hsp', hout', h18', hmf', hinv', hh', hfr'⟩ := ho
      exact ⟨h', hf, ms', hr.trans hr', hp, by rw [hsp', hsp], by rw [hout', hout],
        by rw [h18', h18], hmf2 ms' hmf', hinv', hh', fun k hk => by rw [hfr' k hk, hfr k hk]⟩
  | Break k st' sl' =>
      obtain ⟨t, ht, ms', hr', hp, hsp', hout', h18', hmf', hloc, hcnt, hk, hfr'⟩ := ho
      exact ⟨t, ht, ms', hr.trans hr', hp, by rw [hsp', hsp], by rw [hout', hout],
        by rw [h18', h18], hmf2 ms' hmf', hloc, hcnt, hk, fun j hj => by
          rw [hfr' j hj, hfr j (Nat.lt_of_lt_of_le hj (hctl.bases t (List.mem_of_getElem? ht)))]⟩
  | Return st' vs =>
      obtain ⟨t, ht, ms', hr', hp, hsp', hout', h18', hmf', hk⟩ := ho
      exact ⟨t, ht, ms', hr.trans hr', hp, by rw [hsp', hsp], by rw [hout', hout],
        by rw [h18', h18], hmf2 ms' hmf', hk⟩
  | Trap st' msg =>
      obtain ⟨ms', hr', hout', hpc⟩ := ho
      exact ⟨ms', hr.trans hr', by rw [hout', hout], hpc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-! ## Instruction lists -/

/-- The simulation of instruction lists at fuel `F`. -/
def ListSim (F : Nat) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (h : Nat) (a : UInt64) (p : List Instruction) (is : List Instr)
    (fin : Option Nat), genList E ctl h a p = .ok (is, fin) → CodeAt code a is →
    curBase ctl ≤ h → CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E.locals sl ms → sl.values.length = h → ms.pc = a →
      CallsOk P code F m E.callee E.trapUnreachable E.trapDiv E.trapStack →
      Outcome P code E ctl fin (after a is.length) (Wasm.exec F m st sl p) ms

theorem prog_sim {F : Nat} (hI : ∀ inst, InstrSim P code F inst) : ListSim P code F := by
  intro E ctl h a p
  induction p generalizing h a with
  | nil =>
      intro is fin hg hcode hb hctl α m st sl ms hinv hh hpc hcl
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      rw [ProofKit.exec_nil]
      exact .inr ⟨h, rfl, ms, .refl _, by simp [hpc, after_zero], rfl, rfl, rfl, fun _ _ => rfl,
        hinv, hh, fun _ _ => rfl⟩
  | cons i rest ih =>
      intro is fin hg hcode hb hctl α m st sl ms hinv hh hpc hcl
      obtain ⟨c1, f1, h1, ⟨rfl, his, rfl⟩ | ⟨h', c2, rfl, h2, rfl⟩⟩ := gen_cons hg
      · subst his
        have hi := hI i E ctl h a _ none h1 hcode hb hctl m st sl ms hinv hh hpc hcl
        rw [ProofKit.exec_cons]
        revert hi
        cases execOne F m st sl i with
        | Fallthrough st' sl' =>
            intro hi
            rcases hi with hov | ⟨_, hn, _⟩
            · exact .inl hov
            · cases hn
        | _ => intro hi; exact hi
      · have hc := (CodeAt.append (code := code)).mp hcode
        have hi := hI i E ctl h a c1 (some h') h1 hc.1 hb hctl m st sl ms hinv hh hpc
          hcl
        rw [ProofKit.exec_cons]
        revert hi
        cases execOne F m st sl i with
        | Fallthrough st' sl' =>
            intro hi
            rcases hi with hov | ⟨h'', hn, ms1, hr, hp, hsp, hout, h18, hmf, hinv1, hh1, hfr⟩
            · exact .inl hov
            cases hn
            have ho := ih h' (after a c1.length) c2 fin h2 hc.2 (genInstr_base h1 hb) hctl m st'
              sl' ms1 hinv1 hh1 hp hcl
            rw [after_after, ← List.length_append] at ho
            exact Outcome.trans P code hctl hr hsp hout h18 hmf hfr ho
        | _ => intro hi; exact hi

/-! ## Results of constructs -/

theorem CtlOk.push {ctl : List Ctl} (hctl : CtlOk ctl) {t : Ctl} (hb : curBase ctl ≤ t.base) :
    CtlOk (t :: ctl) :=
  ⟨List.cons_ne_nil _ _, fun t' ht' => by
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact Nat.le_refl _
    · exact Nat.le_trans (hctl.bases t' ht') hb⟩

theorem getLast?_push {t : Ctl} {ctl : List Ctl} (h : ctl ≠ []) :
    (t :: ctl).getLast? = ctl.getLast? := by
  cases ctl with
  | nil => exact absurd rfl h
  | cons c cs => simp

/-- A related stack of height `t.base + t.arity` keeps its top values for a branch to `t`. -/
theorem StackRel.kept {s : State} {vs : List Value} {t : Ctl} (h : StackRel s vs)
    (hlen : vs.length = t.base + t.arity) : Kept t vs s := by
  have h26 := h.1
  refine ⟨by omega, by omega, fun j hj => ?_⟩
  have hv := h.2 (t.base + j) (by omega)
  have e : vs.reverse[t.base + j]'(by simp; omega) = vs[t.arity - 1 - j]'(by omega) := by
    rw [List.getElem_reverse]; congr 1; omega
  rw [e] at hv
  exact hv

/-- The stack after a construct: the values that a branch to it keeps over the stack `below` of
its base, whose registers keep their values. -/
theorem StackRel.of_kept {s s' : State} {t : Ctl} {vs below : List Value} (hk : Kept t vs s')
    (hb : StackRel s below) (hlen : below.length = t.base) (hfr : Frame t.base s s') :
    StackRel s' (vs.take t.arity ++ below) := by
  have hk1 := hk.len
  have hk2 := hk.fits
  refine ⟨by simp; omega, fun k hk' => ?_⟩
  simp only [List.length_append, List.length_take] at hk'
  simp only [List.reverse_append]
  by_cases hkb : k < below.length
  · rw [List.getElem_append_left (by simpa using hkb), hfr k (by omega)]
    exact hb.2 k hkb
  · rw [List.getElem_append_right (by simpa using hkb)]
    have hv := hk.vals (k - t.base) (by omega)
    rw [show t.base + (k - t.base) = k by omega] at hv
    have e : (vs.take t.arity).reverse[k - below.reverse.length]'(by simp; omega) =
        vs[t.arity - 1 - (k - t.base)]'(by omega) := by
      rw [List.getElem_reverse, List.getElem_take]; congr 1; simp; omega
    rw [e]
    exact hv

/-- The outcome of a block or an `if` whose body, under the construct `t` and from `ms1`, gives
`r`, where the machine reaches `ms1` from `ms` with only its program counter changed and the
body's end `endB` leads to `t.target`. -/
theorem construct_outcome {E : Env} {ctl : List Ctl} {α : Type} {r : Continuation α} {t : Ctl}
    {below : List Value} {sl0 : Locals} {ms ms1 : State} {fb : Option Nat} {endB : UInt64}
    (hctl : CtlOk ctl) (hb : curBase ctl ≤ t.base) (hinv : Inv P E.locals sl0 ms)
    (hbelow : StackRel ms below) (hlen : below.length = t.base) (hr1 : Reach P code ms ms1)
    (hsp1 : ms1.sp = ms.sp) (hout1 : ms1.out = ms.out) (hmem1 : ms1.mem = ms.mem)
    (hfr1 : ∀ q, ms1.x q = ms.x q) (hfb : ∀ x, fb = some x → x = t.base + t.arity)
    (hjump : ∀ s : State, s.pc = endB → Reach P code s { s with pc := t.target })
    (ho : Outcome P code E (t :: ctl) fb endB r ms1) :
    Outcome P code E ctl (some (t.base + t.arity)) t.target
      (ProofKit.blockResult t.arity below r) ms := by
  have hmf2 : ∀ ms' : State, MemFrame (ms1.x 18) ms1.sp (E.locals + spillSlots) ms1 ms' →
      MemFrame (ms.x 18) ms.sp (E.locals + spillSlots) ms ms' :=
    fun ms' h b hb => by rw [h b (by rwa [hsp1, hfr1 18]), hmem1]
  rcases ho with ⟨hc, ms', hr', hp, hout'⟩ | ho
  · exact .inl ⟨hc, ms', hr1.trans hr', hp, by rw [hout', hout1]⟩
  refine .inr ?_
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨h', hf, ms', hr', hp, hsp', hout', h18', hmf', hinv', hh', hfr'⟩ := ho
      have hh2 := hfb h' hf
      have hfr2 : Frame t.base ms { ms' with pc := t.target } := fun k hk => by
        show ms'.x (regOf k) = ms.x (regOf k)
        rw [hfr' k hk, hfr1]
      refine ⟨_, rfl, { ms' with pc := t.target }, hr1.trans (hr'.trans (hjump ms' hp)), rfl,
        by show ms'.sp = ms.sp; rw [hsp', hsp1], by show ms'.out = ms.out; rw [hout', hout1],
        by show ms'.x 18 = ms.x 18; rw [h18', hfr1], hmf2 _ hmf', ?_, ?_,
        fun k hk => hfr2 k (Nat.lt_of_lt_of_le hk hb)⟩
      · exact ⟨StackRel.of_kept (StackRel.kept (hinv'.stack.congr fun _ _ => rfl) (by omega))
          hbelow hlen hfr2, hinv'.locals.congr rfl rfl, hinv'.count, hinv'.frame.congr rfl rfl⟩
      · simp; omega
  | Break k st' sl' =>
      obtain ⟨t', ht', ms', hr', hp, hsp', hout', h18', hmf', hloc, hcnt, hk, hfr'⟩ := ho
      have h182 : ms'.x 18 = ms.x 18 := by rw [h18', hfr1]
      cases k with
      | zero =>
          have ht0 : t' = t := by simpa using ht'.symm
          rw [ht0] at hp hk hfr'
          have hfr2 : Frame t.base ms ms' := fun k hk => by rw [hfr' k hk, hfr1]
          have hsp2 : ms'.sp = ms.sp := by rw [hsp', hsp1]
          refine ⟨_, rfl, ms', hr1.trans hr', hp, hsp2, by rw [hout', hout1], h182,
            hmf2 _ hmf', ?_, ?_, fun k hk => hfr2 k (Nat.lt_of_lt_of_le hk hb)⟩
          · exact ⟨StackRel.of_kept hk hbelow hlen hfr2, hloc, hcnt,
              hinv.frame.congr hsp2 h182⟩
          · have := hk.len; simp; omega
      | succ k =>
          refine ⟨t', ht', ms', hr1.trans hr', hp, by rw [hsp', hsp1], by rw [hout', hout1],
            h182, hmf2 _ hmf', hloc, hcnt, hk, fun j hj => by rw [hfr' j hj, hfr1]⟩
  | Return st' vs =>
      obtain ⟨t', ht', ms', hr', hp, hsp', hout', h18', hmf', hk⟩ := ho
      exact ⟨t', by rwa [getLast?_push hctl.nonempty] at ht', ms', hr1.trans hr', hp,
        by rw [hsp', hsp1], by rw [hout', hout1], by rw [h18', hfr1], hmf2 _ hmf', hk⟩
  | Trap st' msg =>
      obtain ⟨ms', hr', hout', hpc⟩ := ho
      exact ⟨ms', hr1.trans hr', by rw [hout', hout1], hpc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim


/-! ## `block`, `loop`, and `if` -/

theorem reach_pc {s : State} {p : UInt64} (h : s.pc = p) : Reach P code s { s with pc := p } := by
  subst h
  exact .refl _

theorem sim_block {f : Nat} (hP : ListSim P code f) (pa ra : Nat) (body : List Instruction)
    (pts rts : List ValueType) : InstrSim P code (f + 1) (.block pa ra body pts rts) := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc hcl
  obtain ⟨rfl, hra, rfl, fb, hl, hfb⟩ := gen_block hgen
  have hn := (genList_size _ h a body is fb hl).1
  simp only [List.map_cons] at hn
  let t : Ctl := { target := after a is.length, arity := ra, base := h }
  have hl' : genList E (t :: ctl) h a body = .ok (is, fb) := by
    show genList E ({ target := after a is.length, arity := ra, base := h } :: ctl) h a body = _
    rw [hn]
    exact hl
  have ho := hP E (t :: ctl) h a body is fb hl' hcode (Nat.le_refl _) (hctl.push hb) m st sl ms
    hinv hh hpc (hcl.mono P code (by omega))
  rw [ProofKit.execOne_block]
  exact construct_outcome P code (t := t) hctl hb hinv hinv.stack hh (.refl _) rfl rfl rfl
    (fun _ => rfl) hfb (fun _ hs => reach_pc P code hs) ho

theorem sim_loop {F : Nat} (hP : ∀ g < F, ListSim P code g) (pa ra : Nat)
    (body : List Instruction) (pts rts : List ValueType) :
    InstrSim P code F (.loop pa ra body pts rts) := by
  suffices key : ∀ g, g ≤ F → InstrSim P code g (.loop pa ra body pts rts) from
    key F (Nat.le_refl _)
  intro g
  induction g with
  | zero =>
      intro _ E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc _
      rw [ProofKit.execOne_zero]
      exact .inr trivial
  | succ f ih =>
      intro hf E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc hcl
      obtain ⟨rfl, hra, rfl, fb, hl, hfb⟩ := gen_loop hgen
      let t : Ctl := { target := a, arity := 0, base := h }
      have ho := hP f (by omega) E (t :: ctl) h a body is fb hl hcode (Nat.le_refl _)
        (hctl.push hb) m st sl ms hinv hh hpc (hcl.mono P code (by omega))
      rw [execOne_loop_succ f m st sl {} 0 ra body pts rts]
      revert ho
      cases Wasm.exec f m st sl body with
      | Fallthrough st' sl' =>
          intro ho
          let t2 : Ctl := { target := after a is.length, arity := ra, base := h }
          exact construct_outcome P code (t := t2) (r := .Fallthrough st' sl') hctl hb hinv
            hinv.stack hh (.refl _) rfl rfl rfl (fun _ => rfl) hfb
            (fun _ hs => reach_pc P code hs) ho
      | Break k st' sl' =>
          intro ho
          rcases ho with hov | ⟨t', ht', ms', hr, hp, hsp, hout, h18, hmf, hloc, hcnt, hk, hfr⟩
          · exact .inl hov
          cases k with
          | zero =>
              have ht0 : t' = t := by simpa using ht'.symm
              rw [ht0] at hp hfr
              have hfr' : Frame h ms ms' := hfr
              have hinv2 : Inv P E.locals
                  { sl' with values := sl'.values.take 0 ++ sl.values.drop 0 } ms' :=
                ⟨hinv.stack.congr fun k hk => hfr' k (by omega), hloc, hcnt,
                  hinv.frame.congr hsp h18⟩
              exact Outcome.trans P code hctl hr hsp hout h18 hmf
                (fun k hk => hfr' k (Nat.lt_of_lt_of_le hk hb))
                (ih (by omega) E ctl h a is _ hgen hcode hb hctl m st' _ ms' hinv2
                  (by simp [hh]) hp (hcl.mono P code (by omega)))
          | succ k =>
              exact .inr ⟨t', ht', ms', hr, hp, hsp, hout, h18, hmf, hloc, hcnt, hk, hfr⟩
      | Return st' vs =>
          intro ho
          rcases ho with hov | ⟨t', ht', rest⟩
          · exact .inl hov
          exact .inr ⟨t', by rwa [getLast?_push hctl.nonempty] at ht', rest⟩
      | Trap st' msg => intro ho; exact ho
      | Invalid _ => intro; exact .inr trivial
      | OutOfFuel => intro; exact .inr trivial
      | ReturnCall _ _ _ => intro ho; exact ho
      | Throwing _ _ _ _ => intro ho; exact ho

theorem exec_iff_cases (f pa ra : Nat) (thn els : List Instruction) (pts rts : List ValueType)
    {α : Type} (m : Module) (st : Store α) (sl : Locals) :
    (∃ x vs, sl.values = .i32 x :: vs) ∨
      ∃ msg, execOne (f + 1) m st sl (.iff pa ra thn els pts rts) = .Invalid msg := by
  cases hv : sl.values with
  | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
  | cons v vs =>
      cases v with
      | i32 x => exact .inl ⟨x, vs, rfl⟩
      | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩

theorem sim_iff {f : Nat} (hP : ListSim P code f) (pa ra : Nat) (thn els : List Instruction)
    (pts rts : List ValueType) : InstrSim P code (f + 1) (.iff pa ra thn els pts rts) := by
  intro E ctl h a is fin hgen hcode hb hctl α m st sl ms hinv hh hpc hcl
  obtain ⟨rfl, hra, hhb, hlt, rfl, ti, ta, ei, ea, g1, g2, hthn, hels, hta, hea, hg1, hg2,
    his⟩ := gen_iff hgen
  have hst := (genList_size _ _ _ thn ti ta hthn).1
  have hse := (genList_size _ _ _ els ei ea hels).1
  simp only [List.map_cons] at hst hse
  have eB : after a (1 + (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (h - 1) thn).1) =
      after (after a 1) ti.length := by
    rw [← hst, after_after]
  have eEnd : after (after (after a
      (1 + (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (h - 1) thn).1)) 1)
      (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (h - 1) els).1 =
      after a is.length := by
    rw [← hst, ← hse, his]
    simp only [after_after, List.length_cons, List.length_append]
    congr 1
    omega
  rw [eEnd] at hthn hels hg2
  rw [eB] at hels hg1 hg2
  have eEndE : after (after (after (after a 1) ti.length) 1) ei.length = after a is.length := by
    rw [his]
    simp only [after_after, List.length_cons, List.length_append]
    congr 1
    omega
  rw [his] at hcode
  have c0 := (CodeAt.cons.mp hcode).1
  have hc1 := (CodeAt.append (code := code)).mp (CodeAt.cons.mp hcode).2
  have cB := (CodeAt.cons.mp hc1.2).1
  have cE := (CodeAt.cons.mp hc1.2).2
  rw [← his] at hcode
  rcases exec_iff_cases f 0 ra thn els pts rts m st sl with ⟨x, vs, hv⟩ | ⟨msg, hex⟩
  · rw [ProofKit.execOne_iff m st sl {} f 0 ra thn els pts rts x vs hv, List.drop_zero]
    have hvl : vs.length = h - 1 := by rw [hv] at hh; simp at hh; omega
    have hst0 := hinv.stack
    rw [hv] at hst0
    have hx : ms.x (regOf (h - 1)) = x.toUInt64 := by
      have := hst0.top; rw [hvl] at this; exact this
    let t : Ctl := { target := after a is.length, arity := ra, base := h - 1 }
    have hctl' : CtlOk (t :: ctl) := hctl.push (show curBase ctl ≤ h - 1 by omega)
    have hcz : code ms.pc = some (encode (.cbz (regOf (h - 1)) g1)) := by rw [hpc]; exact c0
    by_cases hx0 : x = 0
    · rw [ite_eq_right (c := x ≠ 0) (fun hne => hne hx0)]
      have hreg : ms.x (regOf (h - 1)) = 0 := by rw [hx, hx0]; rfl
      have ho := hP E (t :: ctl) (h - 1) _ els ei ea hels cE (Nat.le_refl _) hctl' m st
        { sl with values := vs } _ (Inv.pop P hinv hv _) hvl rfl (hcl.mono P code (by omega))
      exact construct_outcome P code (t := t) hctl (show curBase ctl ≤ h - 1 by omega) hinv
        hst0.pop hvl (cbz_taken P code hcz hpc hg1 hreg) rfl rfl rfl (fun _ => rfl) hea
        (fun _ hs => reach_pc P code (hs.trans eEndE)) ho
    · rw [ite_eq_left hx0]
      have hreg : ms.x (regOf (h - 1)) ≠ 0 := by
        rw [hx]
        exact fun e => hx0 (UInt32.toUInt64_inj.mp (by rw [e]; rfl))
      have ho := hP E (t :: ctl) (h - 1) (after a 1) thn ti ta hthn hc1.1 (Nat.le_refl _) hctl'
        m st { sl with values := vs } { ms with pc := ms.pc + 4 } (Inv.pop P hinv hv _) hvl
        (by simp [hpc, after]) (hcl.mono P code (by omega))
      have hjump : ∀ s : State, s.pc = after (after a 1) ti.length →
          Reach P code s { s with pc := t.target } := by
        intro s hs
        refine reach_exec P code (by rw [hs]; exact cB) ?_ (.refl _)
        show some { s with pc := s.pc + sext 26 g2.val * 4 } =
          some { s with pc := after a is.length }
        rw [hs, bField_target hg2]
      exact construct_outcome P code (t := t) hctl (show curBase ctl ≤ h - 1 by omega) hinv
        hst0.pop hvl (reach_exec P code hcz (cbz_next P hreg) (.refl _)) rfl rfl rfl
        (fun _ => rfl) hta hjump ho
  · rw [hex]
    exact .inr trivial


/-! ## Every instruction and list -/

theorem sim_zero (inst : Instruction) : InstrSim P code 0 inst := by
  intro E ctl h a is fin _ _ _ _ α m st sl ms _ _ _ _
  rw [ProofKit.execOne_zero]
  exact .inr trivial

/-- The simulation of every instruction at fuel `F`, given that of instruction lists at every
fuel below `F`.  The generator rejects the forms outside this case analysis. -/
theorem instr_sim {F : Nat} (hP : ∀ g < F, ListSim P code g) (inst : Instruction) :
    InstrSim P code F inst := by
  cases inst
  case localGet i => exact sim_localGet P code F i
  case localSet i => exact sim_localSet P code F i
  case localTee i => exact sim_localTee P code F i
  case constI64 w => exact sim_constI64 P code F w
  case const c => exact sim_const P code F c
  case eqI64 => exact sim_eqI64 P code F
  case eq => exact sim_eq P code F
  case eqzI64 => exact sim_eqzI64 P code F
  case eqz => exact sim_eqz P code F
  case extendUI32 => exact sim_extendUI32 P code F
  case neI64 => exact sim_neI64 P code F
  case ltUI64 => exact sim_ltUI64 P code F
  case leUI64 => exact sim_leUI64 P code F
  case geUI64 => exact sim_geUI64 P code F
  case addI64 => exact sim_addI64 P code F
  case subI64 => exact sim_subI64 P code F
  case mulI64 => exact sim_mulI64 P code F
  case andI64 => exact sim_andI64 P code F
  case and => exact sim_and P code F
  case orI64 => exact sim_orI64 P code F
  case xorI64 => exact sim_xorI64 P code F
  case shlI64 => exact sim_shlI64 P code F
  case shrUI64 => exact sim_shrUI64 P code F
  case wrapI64 => exact sim_wrapI64 P code F
  case remUI64 => exact sim_remUI64 P code F
  case divUI64 => exact sim_divUI64 P code F
  case unreachable => exact sim_unreachable P code F
  case br n => exact sim_br P code F n
  case br_if n => exact sim_br_if P code F n
  case ret => exact sim_ret P code F
  case block pa ra body pts rts =>
    cases F with
    | zero => exact sim_zero P code _
    | succ f => exact sim_block P code (hP f (by omega)) pa ra body pts rts
  case loop pa ra body pts rts => exact sim_loop P code hP pa ra body pts rts
  case iff pa ra thn els pts rts =>
    cases F with
    | zero => exact sim_zero P code _
    | succ f => exact sim_iff P code (hP f (by omega)) pa ra thn els pts rts
  case call k =>
    cases F with
    | zero => exact sim_zero P code _
    | succ f => exact sim_call P code f k
  all_goals
    intro E ctl h a is fin hgen
    simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hgen

/-- The simulation of instruction lists at every fuel. -/
theorem list_sim (F : Nat) : ListSim P code F := by
  induction F using Nat.strongRecOn with
  | _ F ih => exact prog_sim P code (instr_sim P code ih)


end LeanExe.A64
