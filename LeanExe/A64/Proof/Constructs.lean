import LeanExe.A64.Proof.Control

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
    let n := (listSize (ra :: ctl.map (·.arity)) body).1
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
    let aB := after a (1 + (listSize ar thn).1)
    let aEnd := after (after aB 1) (listSize ar els).1
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
      is.length = (listSize (ctl.map (·.arity)) p).1)
    (hg : genInstr E ctl h a inst = .ok (is, fin)) :
    is.length = (instrSize (ctl.map (·.arity)) inst).1 ∧
      fin.isSome = (instrSize (ctl.map (·.arity)) inst).2 := by
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
      simp only [instrSize, Option.isSome_some, and_true]
      exact hs
  | loop pa ra body pts rts =>
      obtain ⟨-, -, rfl, fb, hl, -⟩ := gen_loop hg
      have hs := ih _ h a body is fb (by simp; omega) hl
      simp only [List.map_cons] at hs
      simp only [instrSize, Option.isSome_some, and_true]
      exact hs
  | iff pa ra thn els pts rts =>
      obtain ⟨-, -, -, -, rfl, ti, ta, ei, ea, f, g, ht, he, -, -, -, -, rfl⟩ := gen_iff hg
      have hst := ih _ _ _ thn ti ta (by simp; omega) ht
      have hse := ih _ _ _ els ei ea (by simp; omega) he
      simp only [List.map_cons] at hst hse
      simp only [instrSize, List.length_cons, List.length_append, Option.isSome_some, and_true]
      omega
  | _ => simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hg

mutual

/-- The generated code of an instruction has the length that `instrSize` computes, and its end
is reachable when `instrSize` says so. -/
theorem genInstr_size {E : Env} : (ctl : List Ctl) → (h : Nat) → (a : UInt64) →
    (inst : Instruction) → (is : List Instr) → (fin : Option Nat) →
    genInstr E ctl h a inst = .ok (is, fin) →
    is.length = (instrSize (ctl.map (·.arity)) inst).1 ∧
      fin.isSome = (instrSize (ctl.map (·.arity)) inst).2
  | _, _, _, _, _, _, hg =>
      genInstr_size_of (fun ctl h a p is fin _ hl => (genList_size ctl h a p is fin hl).1) hg
termination_by _ _ _ inst _ _ _ => sizeOf inst
decreasing_by all_goals (try simp_wf); all_goals omega

/-- The generated code of an instruction list has the length that `listSize` computes, and its
end is reachable when `listSize` says so. -/
theorem genList_size {E : Env} : (ctl : List Ctl) → (h : Nat) → (a : UInt64) →
    (p : List Instruction) → (is : List Instr) → (fin : Option Nat) →
    genList E ctl h a p = .ok (is, fin) →
    is.length = (listSize (ctl.map (·.arity)) p).1 ∧
      fin.isSome = (listSize (ctl.map (·.arity)) p).2
  | ctl, h, a, [], is, fin, hg => by
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      simp [listSize]
  | ctl, h, a, i :: rest, is, fin, hg => by
      obtain ⟨c1, f1, h1, ⟨hf1, his, hfin⟩ | ⟨h', c2, hf1, h2, his⟩⟩ := gen_cons hg
      · subst hf1 his hfin
        have s1 := genInstr_size ctl h a i _ _ h1
        have e2 : (instrSize (ctl.map (·.arity)) i).2 = false := by simpa using s1.2.symm
        simp [listSize, e2, s1.1]
      · subst hf1 his
        have s1 := genInstr_size ctl h a i _ _ h1
        have s2 := genList_size ctl h' (after a c1.length) rest c2 fin h2
        have e2 : (instrSize (ctl.map (·.arity)) i).2 = true := by simpa using s1.2.symm
        simp [listSize, e2, s1.1, s2.1, s2.2]
termination_by _ _ _ p _ _ _ => sizeOf p
decreasing_by all_goals (try simp_wf); all_goals omega

end

end LeanExe.A64
