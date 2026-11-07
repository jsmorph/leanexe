import LeanExe.M7.Proof.Call
import LeanExe.ProofKit.Exec

/-!
The simulation of instruction lists and of `if`, as `LeanExe/A64/Proof/Constructs.lean` states it
for the AArch64 back end.  The generator places an `if`'s branch past the `then` code and its end
at the addresses that `instrSize` and `listSize` compute before it emits the bodies, so the proofs
rest on `genList_size`: the code of a covered list has the length that `listSize` computes, and
every instruction of it takes 4 bytes.  `list_sim` proves the simulation of every covered list at
every fuel by strong induction on the fuel, the fuel at which Talos runs a construct's body and a
call's callee being one less.
-/

namespace LeanExe.M7

open Wasm LeanExe.ProofKit LeanExe.CallGraph

variable {P : Platform} {σ : Nat → UInt32} {code : UInt32 → Option UInt16}

/-! ## Code of 4-byte forms -/

/-- The instruction takes 4 bytes. -/
def Instr.wide (i : Instr) : Bool := i.size == 4

theorem codeSize_of_wide : ∀ {is : List Instr}, is.all Instr.wide = true →
    codeSize is = 4 * is.length
  | [], _ => rfl
  | i :: is, h => by
      simp only [List.all_cons, Bool.and_eq_true, Instr.wide, beq_iff_eq] at h
      rw [codeSize_cons, h.1, codeSize_of_wide h.2, List.length_cons]
      omega

theorem wide_flatten_copies : ∀ {codes : List (List Instr)} {src dst : Nat → Nat},
    (∀ i (hi : i < codes.length), CopyCode codes[i] (src i) (dst i)) →
    codes.flatten.all Instr.wide = true
  | [], _, _, _ => rfl
  | c :: cs, src, dst, h => by
      obtain ⟨h0, h1, h2, h3, rfl⟩ := h 0 (by simp)
      rw [List.flatten_cons, List.all_append,
        wide_flatten_copies (src := fun i => src (i + 1)) (dst := fun i => dst (i + 1))
          fun i hi => h (i + 1) (by simp; omega)]
      rfl

theorem movConst_length (d : Fin 8) (w : Nat) : (movConst d w).length = halfSize w := by
  unfold movConst halfSize; split <;> rfl

theorem movConst_wide (d : Fin 8) (w : Nat) : (movConst d w).all Instr.wide = true := by
  unfold movConst; split <;> rfl

/-! ## The generator's lists and `if` -/

theorem gen_nil {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genList E ctl σs a [] = .ok (is, fin)) :
    is = [] ∧ fin = some σs := by
  simp only [genList, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hg
  exact ⟨hg.1.symm, hg.2.symm⟩

theorem gen_cons {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {i : Instruction} {rest : List Instruction} {is : List Instr} {fin : Option (List ValueType)}
    (hg : genList E ctl σs a (i :: rest) = .ok (is, fin)) :
    ∃ c1 f1, genInstr E ctl σs a i = .ok (c1, f1) ∧
      ((f1 = none ∧ is = c1 ∧ fin = none) ∨
        ∃ σ' c2, f1 = some σ' ∧ genList E ctl σ' (after a c1.length) rest = .ok (c2, fin) ∧
          is = c1 ++ c2) := by
  cases h1 : genInstr E ctl σs a i with
  | error e => simp [genList, h1, bind, Except.bind] at hg
  | ok r =>
      obtain ⟨c1, f1⟩ := r
      refine ⟨c1, f1, rfl, ?_⟩
      cases f1 with
      | none =>
          simp [genList, h1, bind, Except.bind, pure, Except.pure] at hg
          exact .inl ⟨rfl, hg.1.symm, hg.2.symm⟩
      | some σ' =>
          cases h2 : genList E ctl σ' (after a c1.length) rest with
          | error e => simp [genList, h1, h2, bind, Except.bind] at hg
          | ok r2 =>
              obtain ⟨c2, f2⟩ := r2
              simp [genList, h1, h2, bind, Except.bind, pure, Except.pure] at hg
              obtain ⟨rfl, rfl⟩ := hg
              exact .inr ⟨σ', c2, rfl, h2, rfl⟩

theorem any_ne {β : Type} [DecidableEq β] {o : Option β} {n : β}
    (h : ¬ Option.any (fun x => !decide (x = n)) o = true) : ∀ x, o = some x → x = n := by
  intro x hx
  subst hx
  simpa using h

theorem gen_iff {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32} {pa ra : Nat}
    {thn els : List Instruction} {pts rts : List ValueType} {is : List Instr}
    {fin : Option (List ValueType)}
    (hg : genInstr E ctl σs a (.iff pa ra thn els pts rts) = .ok (is, fin)) :
    let ar := ra :: ctl.map (·.arity)
    let aB := after a (3 + (listSize (sigOf E.callee) ar (σs.length - 1) thn).1)
    let aEnd := after (after aB 1) (listSize (sigOf E.callee) ar (σs.length - 1) els).1
    let inner : List Ctl := { target := aEnd, types := rts.reverse, base := σs.length - 1 } :: ctl
    pa = 0 ∧ ra ≤ 1 ∧ rts.length = ra ∧ curBase ctl + 1 ≤ σs.length ∧ σs.head? = some .i32 ∧
      σs.length - 1 < E.frame.height ∧ fin = some (rts.reverse ++ σs.tail) ∧
      ∃ hc ti ta ei ea oq ob, genList E inner σs.tail (after a 3) thn = .ok (ti, ta) ∧
        genList E inner σs.tail (after aB 1) els = .ok (ei, ea) ∧
        (∀ x, ta = some x → x = rts.reverse ++ σs.tail) ∧
        (∀ x, ea = some x → x = rts.reverse ++ σs.tail) ∧
        oq % 2 = 0 ∧ -1048576 ≤ oq ∧ oq < 1048576 ∧
        after a 2 + 4 + UInt32.ofInt oq = after aB 1 ∧
        ob % 2 = 0 ∧ -16777216 ≤ ob ∧ ob < 16777216 ∧ aB + 4 + UInt32.ofInt ob = aEnd ∧
        is = [.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, .cmpImm 0 0,
          Instr.bcondTo condEQ oq] ++ ti ++ [Instr.bTo ob] ++ ei := by
  intro ar aB aEnd inner
  by_cases hc : pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra ∨ σs.length < curBase ctl + 1 ∨
      σs.head? ≠ some .i32
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hc' := hc
  simp only [not_or, Ne, Decidable.not_not, Nat.not_lt, gt_iff_lt] at hc'
  obtain ⟨hpa, hra, hrl, hh, hhead⟩ := hc'
  subst hpa
  simp [genInstr, hhead, show ¬ ra > 1 by omega, hrl, show ¬ σs.length < curBase ctl + 1 by omega,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hg
  split at hg
  · cases hg
  rename_i o ho
  split at hg
  · cases hg
  rename_i c hcimm
  split at hg
  · cases hg
  rename_i v hti
  split at hg
  · cases hg
  rename_i v1 hei
  split at hg
  · cases hg
  rename_i hends
  split at hg
  · cases hg
  rename_i i1 hi1
  split at hg
  · cases hg
  rename_i i2 hi2
  cases hg
  obtain ⟨hlt, rfl⟩ := Env.op_ok ho
  obtain ⟨hc'', rfl⟩ := imm_ok hcimm
  obtain ⟨oq, rfl, q1, q2, q3, q4⟩ := bcondAt_ok hi1
  obtain ⟨ob, rfl, b1, b2, b3, b4⟩ := bAt_ok hi2
  exact ⟨rfl, by omega, hrl, by omega, hhead, hlt, rfl, hc'', v.1, v.2, v1.1, v1.2, oq, ob,
    hti, hei, any_ne (not_or.mp hends).1, any_ne (not_or.mp hends).2, q1, q2, q3, q4, b1, b2, b3,
    b4, by simp⟩

@[simp] theorem Ctl.arity_mk (tg : UInt32) (ts : List ValueType) (b : Nat) :
    (Ctl.mk tg ts b).arity = ts.length := rfl

/-! ## Sizes -/

/-- The generated code of a covered instruction has the length that `instrSize` computes, takes
4 bytes for each instruction, and its end is reachable when `instrSize` says so, given the same
of the covered lists smaller than the instruction. -/
theorem genInstr_size_of {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {inst : Instruction} {is : List Instr} {fin : Option (List ValueType)}
    (hcov : coveredInstr inst = true)
    (ih : ∀ (ctl : List Ctl) (σs : List ValueType) (a : UInt32) (p : List Instruction)
      (is : List Instr) (fin : Option (List ValueType)), sizeOf p < sizeOf inst →
      coveredList p = true → genList E ctl σs a p = .ok (is, fin) →
      is.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) σs.length p).1 ∧
        is.all Instr.wide = true)
    (hg : genInstr E ctl σs a inst = .ok (is, fin)) :
    is.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σs.length inst).1 ∧
      fin.map List.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σs.length inst).2 ∧
      is.all Instr.wide = true := by
  cases inst with
  | localGet i =>
      obtain ⟨t, src, -, -, -, h0, h1, h2, h3, rfl, rfl⟩ := gen_localGet hg
      exact ⟨rfl, rfl, rfl⟩
  | localSet i =>
      obtain ⟨-, -, -, dst, -, h0, h1, h2, h3, rfl, rfl⟩ := gen_localSet hg
      exact ⟨rfl, by simp [instrSize], rfl⟩
  | constI64 v =>
      obtain ⟨-, h0, h1, rfl, rfl⟩ := gen_constI64 hg
      refine ⟨by simp [instrSize, movPair, movConst_length, constSize]; omega, rfl, ?_⟩
      simp only [movPair, List.all_append, movConst_wide, Bool.true_and]
      rfl
  | addI64 | andI64 | orI64 | xorI64 | mulI64 | eqI64 | neI64 =>
      simp only [genInstr] at hg
      obtain ⟨hb2, -, -, -, -, -, -, -, rfl, rfl⟩ := gen_bin hg
      exact ⟨by simp [instrSize, eqOps], by simp [instrSize]; omega, rfl⟩
  | eqzI64 =>
      obtain ⟨hb1, -, -, -, -, -, rfl, rfl⟩ := gen_eqzI64 hg
      exact ⟨rfl, by simp [instrSize]; omega, rfl⟩
  | extendUI32 =>
      obtain ⟨hb1, rfl, rfl⟩ := gen_extendUI32 hg
      exact ⟨rfl, by simp [instrSize]; omega, rfl⟩
  | shlI64 | shrUI64 =>
      simp only [genInstr] at hg
      obtain ⟨hb2, -, -, -, -, -, -, rfl, rfl⟩ := gen_shift hg
      exact ⟨by simp [instrSize, shlOps, shrOps], by simp [instrSize]; omega, rfl⟩
  | divUI64 | remUI64 =>
      simp only [genInstr] at hg
      obtain ⟨hb2, -, -, -, -, -, -, -, oq, ob, -, -, -, -, -, -, -, -, rfl, rfl⟩ := gen_div hg
      exact ⟨by simp [instrSize], by simp [instrSize]; omega, rfl⟩
  | iff pa ra thn els pts rts =>
      obtain ⟨rfl, -, hrl, hb1, -, -, rfl, hc, ti, ta, ei, ea, oq, ob, hti, hei, -, -, -, -, -, -,
        -, -, -, -, rfl⟩ := gen_iff hg
      simp only [coveredInstr, Bool.and_eq_true] at hcov
      have st := ih _ _ _ thn ti ta (by simp; omega) hcov.1 hti
      have se := ih _ _ _ els ei ea (by simp; omega) hcov.2 hei
      simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl, List.length_tail] at st se
      refine ⟨?_, ?_, ?_⟩
      · simp only [instrSize, List.length_append, List.length_cons, List.length_nil, st.1, se.1]
        omega
      · simp only [instrSize, Option.map_some, List.length_append, List.length_reverse, hrl,
          List.length_tail]
        congr 1
        omega
      · simp only [List.all_append, st.2, se.2]
        rfl
  | call k =>
      obtain ⟨target, ps, rs, hk, hbp, -, -, args, res, off, hal, hargs, -, hrl, hres, -, -, -, -, -,
        rfl, rfl⟩ := gen_call hg
      have hsig : sigOf E.callee k = some (ps.length, rs.length) := by simp [sigOf, hk]
      refine ⟨?_, ?_, ?_⟩
      · simp only [instrSize, hsig, List.length_append, length_copies hargs,
          length_copies hres, hal, hrl, List.length_cons, List.length_nil]
        try omega
      · simp only [instrSize, hsig, Option.map_some, List.length_append, List.length_reverse,
          List.length_drop]
        congr 1
        omega
      · simp only [List.all_append, wide_flatten_copies hargs, wide_flatten_copies hres]
        rfl
  | _ => simp [coveredInstr] at hcov

mutual

theorem genInstr_size {E : Env} : (ctl : List Ctl) → (σs : List ValueType) → (a : UInt32) →
    (inst : Instruction) → (is : List Instr) → (fin : Option (List ValueType)) →
    coveredInstr inst = true → genInstr E ctl σs a inst = .ok (is, fin) →
    is.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σs.length inst).1 ∧
      fin.map List.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σs.length inst).2 ∧
      is.all Instr.wide = true
  | _, _, _, _, _, _, hcov, hg =>
      genInstr_size_of hcov (fun ctl σs a p is fin _ hc hl =>
        ⟨(genList_size ctl σs a p is fin hc hl).1, (genList_size ctl σs a p is fin hc hl).2.2⟩) hg
termination_by _ _ _ inst _ _ _ _ => sizeOf inst
decreasing_by all_goals (try simp_wf); all_goals omega

theorem genList_size {E : Env} : (ctl : List Ctl) → (σs : List ValueType) → (a : UInt32) →
    (p : List Instruction) → (is : List Instr) → (fin : Option (List ValueType)) →
    coveredList p = true → genList E ctl σs a p = .ok (is, fin) →
    is.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) σs.length p).1 ∧
      fin.map List.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) σs.length p).2 ∧
      is.all Instr.wide = true
  | ctl, σs, a, [], is, fin, _, hg => by
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      exact ⟨rfl, rfl, rfl⟩
  | ctl, σs, a, i :: rest, is, fin, hc, hg => by
      simp only [coveredList, Bool.and_eq_true] at hc
      obtain ⟨c1, f1, h1, ⟨hf1, his, hfin⟩ | ⟨σ', c2, hf1, h2, his⟩⟩ := gen_cons hg
      · subst hf1 his hfin
        have s1 := genInstr_size ctl σs a i _ _ hc.1 h1
        refine ⟨?_, ?_, s1.2.2⟩
        · simp only [listSize, ← s1.2.1, Option.map_none]
          exact s1.1
        · simp only [listSize, ← s1.2.1, Option.map_none]
      · subst hf1 his
        have s1 := genInstr_size ctl σs a i _ _ hc.1 h1
        have s2 := genList_size ctl σ' (after a c1.length) rest c2 fin hc.2 h2
        refine ⟨?_, ?_, ?_⟩
        · simp only [listSize, ← s1.2.1, Option.map_some, List.length_append, s1.1, s2.1]
        · simp only [listSize, ← s1.2.1, Option.map_some, s2.2.1]
        · rw [List.all_append, s1.2.2, s2.2.2]; rfl
termination_by _ _ _ p _ _ _ _ => sizeOf p
decreasing_by all_goals (try simp_wf); all_goals omega

end

/-! ## Composition -/

theorem genInstr_base {E : Env} {ctl : List Ctl} {σs : List ValueType} {a : UInt32}
    {inst : Instruction} {is : List Instr} {σ' : List ValueType} (hcov : coveredInstr inst = true)
    (hg : genInstr E ctl σs a inst = .ok (is, some σ')) (hb : curBase ctl ≤ σs.length) :
    curBase ctl ≤ σ'.length := by
  cases inst with
  | localGet i => obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := gen_localGet hg; cases he; simp; omega
  | localSet i =>
      obtain ⟨h1, _, _, _, _, _, _, _, _, _, he⟩ := gen_localSet hg; cases he; simp; omega
  | constI64 v => obtain ⟨_, _, _, _, he⟩ := gen_constI64 hg; cases he; simp; omega
  | addI64 | andI64 | orI64 | xorI64 | mulI64 | eqI64 | neI64 =>
      simp only [genInstr] at hg
      obtain ⟨h1, -, -, -, -, -, -, -, -, he⟩ := gen_bin hg
      cases he; simp; omega
  | eqzI64 => obtain ⟨h1, _, _, _, _, _, _, he⟩ := gen_eqzI64 hg; cases he; simp; omega
  | extendUI32 => obtain ⟨h1, _, he⟩ := gen_extendUI32 hg; cases he; simp; omega
  | shlI64 | shrUI64 =>
      simp only [genInstr] at hg
      obtain ⟨h1, -, -, -, -, -, -, -, he⟩ := gen_shift hg
      cases he; simp; omega
  | divUI64 | remUI64 =>
      simp only [genInstr] at hg
      obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he⟩ := gen_div hg
      cases he; simp; omega
  | iff pa ra thn els pts rts =>
      obtain ⟨_, _, _, h1, _, _, he, _⟩ := gen_iff hg
      cases he; simp; omega
  | call k =>
      obtain ⟨_, _, _, _, hbp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ := gen_call hg
      cases he; simp; omega
  | _ => simp [coveredInstr] at hcov

/-- An outcome from a state that the model reaches from `ms` with SP, the device trace, the read
count, the words that `BodyKeeps` names, and the operand slots below the innermost base
unchanged, as an outcome from `ms`. -/
theorem Outcome.trans {E : Env} {ctl : List Ctl} {fin : Option (List ValueType)} {endA : UInt32}
    {α : Type} {r : Continuation α} {ms ms1 : State} (hr : Reach P σ code ms ms1)
    (hsp : ms1.sp = ms.sp) (htr : ms1.trace = ms.trace) (hrd : ms1.reads = ms.reads)
    (hk : BodyKeeps E.frame ms.sp ms ms1) (hb : Below E.frame (curBase ctl) ms ms1)
    (ho : Outcome P σ code E ctl fin endA r ms1) : Outcome P σ code E ctl fin endA r ms := by
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf, ms', hr', hp, hsp', htr', hrd', hk', hb', hinv'⟩ := ho
      rw [hsp] at hk'
      exact ⟨σ', hf, ms', hr.trans hr', hp, hsp'.trans hsp, htr'.trans htr, hrd'.trans hrd,
        hk.trans hk', hb.trans hb' hsp, hinv'⟩
  | Break _ _ _ => exact ho.elim
  | Return _ _ => exact ho.elim
  | Trap _ _ => trivial
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-! ## Instruction lists -/

/-- The simulation of every covered list at fuel `F` from that of every covered instruction. -/
theorem prog_sim {F : Nat} (hI : ∀ inst, coveredInstr inst = true → InstrSim P σ code F inst) :
    ListSim P σ code F := by
  intro E ctl σs a p
  induction p generalizing σs a with
  | nil =>
      intro is fin _ hg hcode hev hdiv hb α m st sl ms hinv hpc need D hcl hD hroom
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      rw [ProofKit.exec_nil]
      exact ⟨σs, rfl, ms, .refl _, by rw [hpc, after_eq]; simp, rfl, rfl, rfl,
        BodyKeeps.refl _ _ _, Below.refl _ _ _, hinv⟩
  | cons i rest ih =>
      intro is fin hc hg hcode hev hdiv hb α m st sl ms hinv hpc need D hcl hD hroom
      simp only [coveredList, Bool.and_eq_true] at hc
      have hDi : ∀ j ∈ callsOf i, need j ≤ D := fun j hj =>
        hD j (by simp only [callsIn]; exact List.mem_append_left _ hj)
      have hDr : ∀ j ∈ callsIn rest, need j ≤ D := fun j hj =>
        hD j (by simp only [callsIn]; exact List.mem_append_right _ hj)
      obtain ⟨c1, f1, h1, ⟨rfl, his, rfl⟩ | ⟨σ', c2, rfl, h2, rfl⟩⟩ := gen_cons hg
      · subst his
        have hi := hI i hc.1 E ctl σs a _ none h1 hcode hev hdiv hb m st sl ms hinv hpc need D hcl
          hDi hroom
        rw [ProofKit.exec_cons]
        revert hi
        cases execOne F m st sl i with
        | Fallthrough st' sl' =>
            intro hi
            obtain ⟨_, hn, _⟩ := hi
            cases hn
        | _ => intro hi; exact hi
      · have hcs := (genInstr_size _ _ _ _ _ _ hc.1 h1).2.2
        have hc' := (CodeAt.append (code := code)).mp hcode
        have hi := hI i hc.1 E ctl σs a c1 (some σ') h1 hc'.1 hev hdiv hb m st sl ms hinv hpc need D
          hcl hDi hroom
        rw [ProofKit.exec_cons]
        revert hi
        cases execOne F m st sl i with
        | Fallthrough st' sl' =>
            intro hi
            obtain ⟨σ'', hn, ms1, hr, hp, hsp, htr, hrd, hk, hbl, hinv1⟩ := hi
            cases hn
            rw [codeSize_of_wide hcs, ← after_eq] at hc'
            have ho := ih σ' (after a c1.length) c2 fin hc.2 h2 hc'.2 (even_after hev _)
              hdiv (genInstr_base hc.1 h1 hb) m st' sl' ms1 hinv1 hp need D hcl hDr
              (by unfold room at *; rw [hsp]; exact hroom)
            rw [after_after, ← List.length_append] at ho
            exact Outcome.trans hr hsp htr hrd hk hbl ho
        | _ => intro hi; exact hi


/-! ## Results of constructs -/

theorem ValAt.of_mem {s t : State} {o : Nat} {v : Value} (h : ValAt s o v) (hsp : t.sp = s.sp)
    (hmem : t.mem = s.mem) : ValAt t o v :=
  h.congr hsp ⟨by rw [hmem], by rw [hmem]⟩

theorem Below.of_mem {fr : Frame} {b : Nat} {s t : State} (hmem : t.mem = s.mem) :
    Below fr b s t :=
  fun _ _ => ⟨by rw [hmem], by rw [hmem]⟩

/-- The relation after the pop of the top `v` of the stack `v :: vs`, at a state with the SP and
the memory of `ms`. -/
theorem Inv.pop {E : Env} {σs : List ValueType} {sl : Locals} {ms ms1 : State} {v : Value}
    {vs : List Value} (hinv : Inv P E σs sl ms) (hv : sl.values = v :: vs) (hsp : ms1.sp = ms.sp)
    (hmem : ms1.mem = ms.mem) : Inv P E σs.tail { sl with values := vs } ms1 := by
  have hh := hinv.height
  rw [hv] at hh
  refine ⟨by simp at hh ⊢; omega, fun h v' hv' => ?_, hinv.count,
    fun i v' o h1 h2 => (hinv.locals i v' o h1 h2).of_mem hsp hmem, hinv.ltypes,
    hinv.frame.congr hsp, ?_⟩
  · have hl : h < vs.length := getElem?_reverse_lt hv'
    exact (hinv.stack h v' (by rw [hv, getElem?_reverse_cons hl]; exact hv')).of_mem hsp hmem
  · have h1 := hinv.types
    rw [hv] at h1
    exact h1.tail

/-- The outcome of a construct whose body, under the construct `t` and from `ms1`, gives `r`,
where the model reaches `ms1` from `ms` with SP and the memory unchanged and the end `endB` of the
body leads to `endT`, over the stack `below` of the types `σb`. -/
theorem construct_outcome {E : Env} {ctl : List Ctl} {α : Type} {r : Continuation α} {t : Ctl}
    {below : List Value} {σb : List ValueType} {ms ms1 : State} {fb : Option (List ValueType)}
    {endB endT : UInt32} {ra : Nat} (hra : t.types.length = ra) (hb : curBase ctl ≤ t.base)
    (hbelow : ∀ h v, below.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v)
    (hbt : Typed σb below) (hlen : below.length = t.base) (hr1 : Reach P σ code ms ms1)
    (hsp1 : ms1.sp = ms.sp) (htr1 : ms1.trace = ms.trace) (hrd1 : ms1.reads = ms.reads)
    (hmem1 : ms1.mem = ms.mem) (hfb : ∀ x, fb = some x → x = t.types ++ σb)
    (hjump : ∀ s : State, s.pc = endB → ∃ s', Reach P σ code s s' ∧ s'.pc = endT ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.trace = s.trace ∧ s'.reads = s.reads)
    (ho : Outcome P σ code E (t :: ctl) fb endB r ms1) :
    Outcome P σ code E ctl (some (t.types ++ σb)) endT (ProofKit.blockResult ra below r) ms := by
  subst hra
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf, ms2, hr2, hp2, hsp2, htr2, hrd2, hk2, hb2, hinv2⟩ := ho
      have hσ' := hfb σ' hf
      subst hσ'
      obtain ⟨ms3, hr3, hp3, hsp3, hmem3, htr3, hrd3⟩ := hjump ms2 hp2
      have hty' := hinv2.types
      have hl' : sl'.values.length = t.types.length + t.base := by
        rw [← hty'.length, List.length_append, hbt.length, hlen]
      rw [hsp1] at hk2
      have hsp21 : ms2.sp = ms.sp := hsp2.trans hsp1
      refine ⟨_, rfl, ms3, hr1.trans (hr2.trans hr3), hp3, by rw [hsp3, hsp21],
        by rw [htr3, htr2, htr1], by rw [hrd3, hrd2, hrd1],
        ((BodyKeeps.of_mem hmem1).trans hk2).trans (BodyKeeps.of_mem hmem3), ?_, ?_⟩
      · exact ((Below.of_mem hmem1).trans (hb2.mono hb) hsp1).trans (Below.of_mem hmem3) hsp21
      · refine ⟨by have := hinv2.height; simp [hlen]; omega, fun h v hv => ?_, hinv2.count,
          fun i v o h1 h2 => (hinv2.locals i v o h1 h2).of_mem hsp3 hmem3, hinv2.ltypes,
          hinv2.frame.congr hsp3, ?_⟩
        · change (sl'.values.take t.types.length ++ below).reverse[h]? = some v at hv
          rw [List.reverse_append] at hv
          by_cases hh : h < below.length
          · rw [List.getElem?_append_left (by simpa using hh)] at hv
            have h1 : SlotSame ms ms3 (E.frame.opAt h) :=
              ((SlotSame.trans (⟨by rw [hmem1], by rw [hmem1]⟩ : SlotSame ms ms1 _)
                (hb2 h (by show h < t.base; omega)) hsp1).trans
                (⟨by rw [hmem3], by rw [hmem3]⟩ : SlotSame ms2 ms3 _) hsp21)
            exact (hbelow h v hv).congr (by rw [hsp3, hsp21]) h1
          · rw [List.getElem?_append_right (by simp; omega)] at hv
            simp only [List.length_reverse] at hv
            have e : sl'.values.reverse[h]? = some v := by
              rw [← List.take_append_drop t.types.length sl'.values, List.reverse_append,
                List.getElem?_append_right (by simp; omega)]
              simp only [List.length_reverse, List.length_drop]
              rw [show h - (sl'.values.length - t.types.length) = h - below.length by omega]
              exact hv
            exact (hinv2.stack h v e).of_mem hsp3 hmem3
        · have := hty'.take t.types.length
          rw [List.take_left] at this
          exact this.append hbt
  | Break k _ _ => exact ho.elim
  | Return _ _ => exact ho.elim
  | Trap _ _ => trivial
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-- The code of `l1 ++ l2`, where every instruction of `l1` takes 4 bytes, places `l2` the
length of `l1` in instructions on. -/
theorem CodeAt.split_wide {a : UInt32} {l1 l2 : List Instr} (h : CodeAt code a (l1 ++ l2))
    (hw : l1.all Instr.wide = true) : CodeAt code a l1 ∧ CodeAt code (after a l1.length) l2 := by
  obtain ⟨h1, h2⟩ := CodeAt.append.mp h
  rw [codeSize_of_wide hw, ← after_eq] at h2
  exact ⟨h1, h2⟩

/-! ## `if` -/

theorem sim_iff {f : Nat} (hP : ListSim P σ code f) (pa ra : Nat) (thn els : List Instruction)
    (pts rts : List ValueType) (hct : coveredList thn = true) (hce : coveredList els = true) :
    InstrSim P σ code (f + 1) (.iff pa ra thn els pts rts) := by
  intro E ctl σs a is fin hgen hcode hev hdiv hb α m st sl ms hinv hpc need D hcl hD hroom
  obtain ⟨rfl, -, hrl, hb1, hhead, hlt, rfl, hc, ti, ta, ei, ea, oq, ob, hti, hei, hta, hea,
    q1, q2, q3, q4, b1, b2, b3, b4, his⟩ := gen_iff hgen
  have st0 := genList_size _ _ _ thn ti ta hct hti
  have se0 := genList_size _ _ _ els ei ea hce hei
  simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl, List.length_tail] at st0 se0
  have hDt : ∀ j ∈ callsIn thn, need j ≤ D := fun j hj =>
    hD j (by simp only [callsOf]; exact List.mem_append_left _ hj)
  have hDe : ∀ j ∈ callsIn els, need j ≤ D := fun j hj =>
    hD j (by simp only [callsOf]; exact List.mem_append_right _ hj)
  generalize (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (σs.length - 1) thn).1 = Lt
    at *
  generalize (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (σs.length - 1) els).1 = Le
    at *
  have htl : ti.length = Lt := st0.1
  have hel : ei.length = Le := se0.1
  have hend : after a is.length = after (after (after a (3 + Lt)) 1) Le := by
    rw [his]
    simp only [List.length_append, List.length_cons, List.length_nil, htl, hel, after_after]
  rw [hend]
  rw [his] at hcode
  -- the condition
  have hh := hinv.len
  obtain ⟨c, vs, hv⟩ := hinv.types.i32_head hhead
  rw [ProofKit.execOne_iff m st sl {} f 0 ra thn els pts rts c vs hv, List.drop_zero]
  have hvl : vs.length = σs.length - 1 := by rw [hv] at hh; simp at hh; omega
  have htop : ValAt ms (E.frame.opAt (σs.length - 1)) (.i32 c) := by
    have := hinv.stack vs.length (.i32 c) (by
      rw [hv, List.reverse_cons, List.getElem?_append_right (by simp), List.length_reverse,
        Nat.sub_self, List.getElem?_cons_zero])
    rwa [hvl] at this
  have hc32 : load32 ms.mem (ms.sp + UInt32.ofNat (E.frame.opAt (σs.length - 1))) = c := htop.1
  have hty := hinv.types
  rw [hv] at hty
  obtain ⟨hk8, hklr, hlrs⟩ := E.frame.opAt_bounds hlt
  -- the pieces of the code
  let L : List Instr := [Instr.ldrSp 0 ⟨E.frame.opAt (σs.length - 1), hc⟩, Instr.cmpImm 0 0]
  have hcode' : CodeAt code a (L ++ [Instr.bcondTo condEQ oq] ++ ti ++ [Instr.bTo ob] ++ ei) :=
    hcode
  have wQ : (L ++ [Instr.bcondTo condEQ oq]).all Instr.wide = true := rfl
  have wT : (L ++ [Instr.bcondTo condEQ oq] ++ ti).all Instr.wide = true := by
    rw [List.all_append, wQ, st0.2.2]
    try rfl
  have wB : (L ++ [Instr.bcondTo condEQ oq] ++ ti ++ [Instr.bTo ob]).all Instr.wide = true := by
    rw [List.all_append, wT]
    try rfl
  obtain ⟨hc4, hcE⟩ := hcode'.split_wide wB
  obtain ⟨hc3, hcB⟩ := hc4.split_wide wT
  obtain ⟨hc2, hcT⟩ := hc3.split_wide wQ
  obtain ⟨hcL, hcQ⟩ := hc2.split_wide (rfl : L.all Instr.wide = true)
  rw [show (L ++ [Instr.bcondTo condEQ oq] ++ ti ++ [Instr.bTo ob]).length = 3 + Lt + 1 by
    rw [List.length_append, List.length_append, htl]
    try rfl, ← after_after] at hcE
  rw [show (L ++ [Instr.bcondTo condEQ oq] ++ ti).length = 3 + Lt by
    rw [List.length_append, htl]
    try rfl] at hcB
  rw [show (L ++ [Instr.bcondTo condEQ oq]).length = 3 from rfl] at hcT
  rw [show L.length = 2 from rfl] at hcQ
  -- `LDR`, `CMP`, and `BEQ`
  have hok : SlotsOk P ms.sp L :=
    slotsOk_ld (hinv.frame.word (by omega) (by omega))
      (slotsOk_cons rfl (fun o ho => by cases ho) (slotsOk_nil _))
  rw [← hpc] at hcL
  obtain ⟨r1, p1, sp1, -, tr1, rd1, -⟩ := run_slots (σ := σ) hok hcL
  have hz : (slotRun P σ L ms).zFlag = (c == 0) := by
    simp only [L, slotRun_cons, slotRun_nil, slotStep, exec, Option.getD_some]
    state_simp
    first | rw [cmp_imm0] | rw [cmp_zero]
    exact congrArg (· == 0) hc32
  have hm : (slotRun P σ L ms).mem = ms.mem := rfl
  have hBpc : (slotRun P σ L ms).pc = after a 2 := by
    rw [p1, hpc, after_eq]
    try rfl
  rw [← hBpc] at hcQ
  have rB := reach_bcondTo (P := P) (σ := σ) q1 q2 q3 hcQ
  have hc0 : (slotRun P σ L ms).condHolds 0 = (c == 0) := by rw [condHolds_eq, hz]
  rw [show condEQ = (0 : Fin 14) from rfl, hc0] at rB
  let t : Ctl :=
    { target := after (after (after a (3 + Lt)) 1) Le, types := rts.reverse,
      base := σs.length - 1 }
  have hbase : curBase (t :: ctl) ≤ σs.tail.length := by
    show σs.length - 1 ≤ σs.tail.length
    rw [List.length_tail]
    exact Nat.le_refl _
  have hroom' : ∀ s : State, s.sp = ms.sp → D ≤ room E s := fun s hs => by
    unfold room at *
    rw [hs]
    exact hroom
  have hbelow : ∀ h v, vs.reverse[h]? = some v → ValAt ms (E.frame.opAt h) v := fun h v hv' =>
    hinv.stack h v (by rw [hv, getElem?_reverse_cons (getElem?_reverse_lt hv')]; exact hv')
  have hcl' := CallsOk.mono P σ code hcl (Nat.le_succ f)
  by_cases hcz : c = 0
  · -- the `else` branch
    rw [ite_eq_right (fun h => h hcz)]
    rw [show (c == 0) = true by simp [hcz], ite_eq_left rfl] at rB
    obtain ⟨u1, hu1d⟩ : ∃ u1 : State,
        u1 = { slotRun P σ L ms with pc := (slotRun P σ L ms).pc + 4 + UInt32.ofInt oq } :=
      ⟨_, rfl⟩
    have rB' : Reach P σ code (slotRun P σ L ms) u1 := by rw [hu1d]; exact rB
    have hu1pc : u1.pc = after (after a (3 + Lt)) 1 := by
      rw [hu1d, State.pc_withPc, hBpc]; exact q4
    have hu1sp : u1.sp = ms.sp := by rw [hu1d, State.sp_withPc]; exact sp1
    have hu1m : u1.mem = ms.mem := by rw [hu1d, State.mem_withPc]; exact hm
    have hu1tr : u1.trace = ms.trace := by rw [hu1d, State.trace_withPc]; exact tr1
    have hu1rd : u1.reads = ms.reads := by rw [hu1d, State.reads_withPc]; exact rd1
    have ho := hP E (t :: ctl) σs.tail _ els ei ea hce hei hcE (even_after (even_after hev _) _)
      hdiv hbase m st { sl with values := vs } u1 (Inv.pop hinv hv hu1sp hu1m) hu1pc need D hcl'
      hDe (hroom' u1 hu1sp)
    rw [hel] at ho
    exact construct_outcome (t := t) (below := vs) (σb := σs.tail)
      (by show rts.reverse.length = ra; rw [List.length_reverse, hrl])
      (show curBase ctl ≤ σs.length - 1 by omega) hbelow hty.tail hvl (r1.trans rB') hu1sp
      hu1tr hu1rd hu1m hea (fun s hs => ⟨s, .refl _, hs, rfl, rfl, rfl, rfl⟩) ho
  · -- the `then` branch
    rw [ite_eq_left hcz]
    rw [show (c == 0) = false from beq_false_of_ne hcz, ite_eq_right Bool.false_ne_true] at rB
    obtain ⟨u1, hu1d⟩ : ∃ u1 : State,
        u1 = { slotRun P σ L ms with pc := (slotRun P σ L ms).pc + 4 } := ⟨_, rfl⟩
    have rB' : Reach P σ code (slotRun P σ L ms) u1 := by rw [hu1d]; exact rB
    have hu1pc : u1.pc = after a 3 := by
      rw [hu1d, State.pc_withPc, hBpc]
      try addr_after
    have hu1sp : u1.sp = ms.sp := by rw [hu1d, State.sp_withPc]; exact sp1
    have hu1m : u1.mem = ms.mem := by rw [hu1d, State.mem_withPc]; exact hm
    have hu1tr : u1.trace = ms.trace := by rw [hu1d, State.trace_withPc]; exact tr1
    have hu1rd : u1.reads = ms.reads := by rw [hu1d, State.reads_withPc]; exact rd1
    have ho := hP E (t :: ctl) σs.tail _ thn ti ta hct hti hcT (even_after hev _) hdiv hbase m st
      { sl with values := vs } u1 (Inv.pop hinv hv hu1sp hu1m) hu1pc need D hcl' hDt
      (hroom' u1 hu1sp)
    rw [htl, after_after] at ho
    exact construct_outcome (t := t) (below := vs) (σb := σs.tail)
      (by show rts.reverse.length = ra; rw [List.length_reverse, hrl])
      (show curBase ctl ≤ σs.length - 1 by omega) hbelow hty.tail hvl (r1.trans rB') hu1sp
      hu1tr hu1rd hu1m hta
      (fun s hs => ⟨_, reach_exec (by rw [hs]; exact hcB) (exec_bTo b1 b2 b3 s) (.refl _),
        by rw [State.pc_withPc, hs]; exact b4, State.sp_withPc _ _, State.mem_withPc _ _,
        State.trace_withPc _ _, State.reads_withPc _ _⟩) ho

/-! ## Every covered instruction and list -/

theorem sim_zero (inst : Instruction) : InstrSim P σ code 0 inst := by
  intro E ctl σs a is fin _ _ _ _ _ α m st sl ms _ _ _ _ _ _ _
  rw [ProofKit.execOne_zero]
  trivial

/-- The simulation of every covered instruction at fuel `F`, given that of covered lists at every
fuel below `F`. -/
theorem instr_sim {F : Nat} (hP : ∀ g < F, ListSim P σ code g) (inst : Instruction)
    (hcov : coveredInstr inst = true) : InstrSim P σ code F inst := by
  cases inst <;> simp only [coveredInstr, Bool.false_eq_true] at hcov
  case localGet i => exact sim_localGet F i
  case localSet i => exact sim_localSet F i
  case constI64 v => exact sim_constI64 F v
  case andI64 => exact sim_andI64 F
  case orI64 => exact sim_orI64 F
  case xorI64 => exact sim_xorI64 F
  case addI64 => exact sim_addI64 F
  case mulI64 => exact sim_mulI64 F
  case eqI64 => exact sim_eqI64 F
  case neI64 => exact sim_neI64 F
  case eqzI64 => exact sim_eqzI64 F
  case extendUI32 => exact sim_extendUI32 F
  case shlI64 => exact sim_shlI64 F
  case shrUI64 => exact sim_shrUI64 F
  case divUI64 => exact sim_divUI64 F
  case remUI64 => exact sim_remUI64 F
  case iff pa ra thn els pts rts =>
    simp only [Bool.and_eq_true] at hcov
    cases F with
    | zero => exact sim_zero _
    | succ f => exact sim_iff (hP f (by omega)) pa ra thn els pts rts hcov.1 hcov.2
  case call k =>
    cases F with
    | zero => exact sim_zero _
    | succ f => exact sim_call f k

/-- The simulation of covered instruction lists at every fuel. -/
theorem list_sim (F : Nat) : ListSim P σ code F := by
  induction F using Nat.strongRecOn with
  | _ F ih => exact prog_sim (instr_sim ih)

end LeanExe.M7
