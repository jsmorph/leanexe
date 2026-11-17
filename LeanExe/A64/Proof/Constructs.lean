import LeanExe.A64.Proof.Control
import LeanExe.A64.Proof.Call
import LeanExe.A64.Proof.Memory
import LeanExe.A64.Proof.ByteMemory
import LeanExe.A64.Proof.Float32
import LeanExe.ProofKit.Exec
import Interpreter.Wasm.Semantics.Lemmas

/-!
The simulation of instruction lists and of the constructs `block`, `loop`, and `if`.  The
generator places a construct's end, which a branch to a block or an `if` targets, at the address
that the size functions `instrSize` and `listSize` compute before it generates the body, so the
proofs rest on the lemma that the generated code has the length that those functions compute.

The proofs hold over every `Machine`: the constructs' own code runs in the program's model, which
`Machine.lift` and `Machine.lift_pc` carry into the machine, and the forms other than the
constructs and calls carry their proofs in the program's model over by `InstrSim.of_leaf`.  The
theorems of the program's model follow at `bare P code α`.
-/

namespace LeanExe.A64

open Wasm

variable (P : Platform) (code : UInt64 → Option UInt32)

/-! ## The generator's constructs and lists -/

@[simp] theorem Ctl.arity_mk (tg : UInt64) (ts : List ValueType) (b : Nat) :
    (Ctl.mk tg ts b).arity = ts.length := rfl

theorem any_ne {β : Type} [DecidableEq β] {o : Option β} {n : β}
    (h : ¬ Option.any (fun x => !decide (x = n)) o = true) : ∀ x, o = some x → x = n := by
  intro x hx
  subst hx
  simpa using h

theorem gen_block {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {pa ra : Nat}
    {body : List Instruction} {pts rts : List ValueType} {is : List Instr}
    {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.block pa ra body pts rts) = .ok (is, fin)) :
    let n := (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) σ.length body).1
    pa = 0 ∧ ra ≤ 1 ∧ rts.length = ra ∧ fin = some (rts.reverse ++ σ) ∧ ∃ fb,
      genList E ({ target := after a n, types := rts.reverse, base := σ.length } :: ctl) σ a
        body = .ok (is, fb) ∧ ∀ x, fb = some x → x = rts.reverse ++ σ := by
  intro n
  by_cases hc : pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hpa : pa = 0 := by omega
  have hra : ¬ ra > 1 := by omega
  have hrl : rts.length = ra := by omega
  subst hpa
  simp [genInstr, hra, hrl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hg
  split at hg
  · cases hg
  rename_i v hl
  split at hg
  · cases hg
  rename_i hend
  cases hg
  exact ⟨rfl, by omega, hrl, rfl, v.2, hl, any_ne hend⟩

theorem gen_loop {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {pa ra : Nat}
    {body : List Instruction} {pts rts : List ValueType} {is : List Instr}
    {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.loop pa ra body pts rts) = .ok (is, fin)) :
    pa = 0 ∧ ra ≤ 1 ∧ rts.length = ra ∧ fin = some (rts.reverse ++ σ) ∧ ∃ fb,
      genList E ({ target := a, types := [], base := σ.length } :: ctl) σ a body = .ok (is, fb) ∧
        ∀ x, fb = some x → x = rts.reverse ++ σ := by
  by_cases hc : pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hpa : pa = 0 := by omega
  have hra : ¬ ra > 1 := by omega
  have hrl : rts.length = ra := by omega
  subst hpa
  simp [genInstr, hra, hrl, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hg
  split at hg
  · cases hg
  rename_i v hl
  split at hg
  · cases hg
  rename_i hend
  cases hg
  exact ⟨rfl, by omega, hrl, rfl, v.2, hl, any_ne hend⟩

theorem gen_iff {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {pa ra : Nat}
    {thn els : List Instruction} {pts rts : List ValueType} {is : List Instr}
    {fin : Option (List ValueType)}
    (hg : genInstr E ctl σ a (.iff pa ra thn els pts rts) = .ok (is, fin)) :
    let ar := ra :: ctl.map (·.arity)
    let aB := after a (1 + (listSize (sigOf E.callee) ar (σ.length - 1) thn).1)
    let aEnd := after (after aB 1) (listSize (sigOf E.callee) ar (σ.length - 1) els).1
    let inner : List Ctl := { target := aEnd, types := rts.reverse, base := σ.length - 1 } :: ctl
    pa = 0 ∧ ra ≤ 1 ∧ rts.length = ra ∧ curBase ctl + 1 ≤ σ.length ∧ σ.length - 1 < 26 ∧
      fin = some (rts.reverse ++ σ.tail) ∧
      ∃ ti ta ei ea f g, genList E inner σ.tail (after a 1) thn = .ok (ti, ta) ∧
        genList E inner σ.tail (after aB 1) els = .ok (ei, ea) ∧
        (∀ x, ta = some x → x = rts.reverse ++ σ.tail) ∧
        (∀ x, ea = some x → x = rts.reverse ++ σ.tail) ∧
        cbField a (after aB 1) = .ok f ∧ bField aB aEnd = .ok g ∧
        is = .cbz (regOf (σ.length - 1)) f :: (ti ++ .b g :: ei) := by
  intro ar aB aEnd inner
  by_cases hc : pa ≠ 0 ∨ ra > 1 ∨ rts.length ≠ ra ∨ σ.length < curBase ctl + 1
  · simp [genInstr, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hg
  have hpa : pa = 0 := by omega
  have hra : ¬ ra > 1 := by omega
  have hrl : rts.length = ra := by omega
  have hh : ¬ σ.length < curBase ctl + 1 := by omega
  subst hpa
  by_cases hlt : σ.length - 1 < 26
  · simp [genInstr, hra, hrl, hh, opReg_ok hlt, bind, Except.bind, pure, Except.pure, throw,
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
    exact ⟨rfl, by omega, hrl, by omega, hlt, rfl, v.1, v.2, v1.1, v1.2, f, g, hthn, hels,
      any_ne (not_or.mp hends).1, any_ne (not_or.mp hends).2, hf, hb, rfl⟩
  · obtain ⟨e, he⟩ := opReg_error hlt
    simp [genInstr, hra, hrl, hh, he, bind, Except.bind] at hg

theorem gen_nil {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    {fin : Option (List ValueType)} (hg : genList E ctl σ a [] = .ok (is, fin)) :
    is = [] ∧ fin = some σ := by
  simp [genList, pure, Except.pure] at hg
  simp [hg]

theorem gen_cons {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64} {i : Instruction}
    {rest : List Instruction} {is : List Instr} {fin : Option (List ValueType)}
    (hg : genList E ctl σ a (i :: rest) = .ok (is, fin)) :
    ∃ c1 f1, genInstr E ctl σ a i = .ok (c1, f1) ∧
      ((f1 = none ∧ is = c1 ∧ fin = none) ∨
        ∃ σ' c2, f1 = some σ' ∧ genList E ctl σ' (after a c1.length) rest = .ok (c2, fin) ∧
          is = c1 ++ c2) := by
  cases h1 : genInstr E ctl σ a i with
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

theorem branchTo_length {t : Ctl} {σ : List ValueType} {a : UInt64} {is : List Instr}
    (hg : branchTo t σ a = .ok is) : is.length = t.arity + 1 := by
  obtain ⟨-, ha1, -, -, f, -, rfl⟩ := gen_branchTo hg
  by_cases h1 : t.arity = 1
  · simp [h1]
  · simp [h1]; omega

/-! ## Sizes -/

/-- The generated code of an instruction has the length that `instrSize` computes, and its end
is reachable when `instrSize` says so, given that the generated code of each instruction list
smaller than the instruction has the length that `listSize` computes. -/
theorem genInstr_size_of {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64}
    {inst : Instruction} {is : List Instr} {fin : Option (List ValueType)}
    (ih : ∀ (ctl : List Ctl) (σ : List ValueType) (a : UInt64) (p : List Instruction)
      (is : List Instr) (fin : Option (List ValueType)), sizeOf p < sizeOf inst →
      genList E ctl σ a p = .ok (is, fin) →
      is.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) σ.length p).1)
    (hg : genInstr E ctl σ a inst = .ok (is, fin)) :
    is.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σ.length inst).1 ∧
      fin.map List.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σ.length inst).2 := by
  cases inst with
  | localGet i => obtain ⟨_, _, _, rfl, rfl⟩ := gen_localGet hg; simp [instrSize]
  | localSet i =>
      obtain ⟨_, _, _, _, _, rfl, rfl⟩ := gen_localStore (.inl ⟨rfl, rfl⟩) hg; simp [instrSize]
  | localTee i =>
      obtain ⟨_, _, _, _, _, rfl, rfl⟩ := gen_localStore (.inr ⟨rfl, rfl⟩) hg; simp [instrSize]
  | constI64 w =>
      obtain ⟨_, rfl, rfl⟩ := gen_const (.inl ⟨rfl, rfl⟩) hg; simp [instrSize, movImm]
  | const c =>
      obtain ⟨_, rfl, rfl⟩ := gen_const (.inr (.inl ⟨c, rfl, rfl, rfl⟩)) hg
      simp [instrSize, movImm]
  | f64Const w =>
      obtain ⟨_, rfl, rfl⟩ := gen_const (.inr (.inr (.inl ⟨rfl, rfl⟩))) hg
      simp [instrSize, movImm]
  | f32Const c =>
      obtain ⟨_, rfl, rfl⟩ := gen_const (.inr (.inr (.inr ⟨c, rfl, rfl, rfl⟩))) hg
      simp [instrSize, movImm]
  | f32Add | f32Sub | f32Mul | f32Div =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genFBin32_ok hg
      simp [instrSize, fBin32]
      omega
  | f32Eq | f32Lt | f32Le =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genFCmp32_ok hg
      simp [instrSize, fCmp32]
      omega
  | f32Sqrt | f32Nearest =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, unCode32]
      omega
  | f32Abs =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, absCode32]
      omega
  | f32ConvertI64U | f32ConvertI32S =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, toS32]
      omega
  | i64TruncSatF32U | i32TruncSatF32S =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, ofS32]
      omega
  | f32ReinterpretI32 | i32ReinterpretF32 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize]
      omega
  | f64Add | f64Sub | f64Mul | f64Div =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genFBin_ok hg
      simp [instrSize, fBin]
      omega
  | f64Eq | f64Lt | f64Le =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genFCmp_ok hg
      simp [instrSize, fCmp]
      omega
  | f64Sqrt =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, sqrtCode]
      omega
  | f64Abs =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, absCode]
      omega
  | f64ConvertI64U =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, convertCode]
      omega
  | i64TruncSatF64U =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize, truncCode]
      omega
  | i64ReinterpretF64 | f64ReinterpretI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genUn_ok hg
      simp [instrSize]
      omega
  | eqI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_cmp (.inl rfl) hg; simp [instrSize]; omega
  | eq => obtain ⟨_, _, rfl, rfl⟩ := gen_cmp (.inr rfl) hg; simp [instrSize]; omega
  | eqzI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_eqz (.inl rfl) hg; simp [instrSize]; omega
  | eqz => obtain ⟨_, _, rfl, rfl⟩ := gen_eqz (.inr rfl) hg; simp [instrSize]; omega
  | neI64 | ltUI64 | leUI64 | geUI64 | ltSI64 | leSI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genCmp_ok hg
      simp [instrSize]
      omega
  | shrSI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_shrS hg; simp [instrSize, sarCode]; omega
  | addI64 | subI64 | mulI64 | andI64 | and | orI64 | xorI64 | shlI64 | shrUI64 =>
      simp only [genInstr] at hg
      obtain ⟨_, _, rfl, rfl⟩ := genBin_ok hg
      simp [instrSize]
      omega
  | wrapI64 => obtain ⟨_, _, rfl, rfl⟩ := gen_wrap hg; simp [instrSize]; omega
  | extendUI32 => obtain ⟨_, rfl, rfl⟩ := gen_extend hg; simp [instrSize]; omega
  | remUI64 =>
      obtain ⟨_, _, _, _, rfl, rfl⟩ := gen_divrem (.inl ⟨rfl, rfl⟩) hg; simp [instrSize]; omega
  | divUI64 =>
      obtain ⟨_, _, _, _, rfl, rfl⟩ := gen_divrem (.inr ⟨rfl, rfl⟩) hg; simp [instrSize]; omega
  | unreachable => obtain ⟨_, _, rfl, rfl⟩ := gen_unreachable hg; simp [instrSize]
  | globalGet i => obtain ⟨_, _, _, rfl, rfl⟩ := gen_globalGet hg; simp [instrSize]
  | globalSet i =>
      obtain ⟨_, h1, _, _, rfl, rfl⟩ := gen_globalSet hg; simp [instrSize]
  | memorySize => obtain ⟨_, rfl, rfl⟩ := gen_memorySize hg; simp [instrSize]
  | memoryGrow =>
      obtain ⟨_, _, _, _, _, rfl, his⟩ := gen_memoryGrow hg
      rcases his with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
      · simp [instrSize, growNarrow, movImm]
      · simp [instrSize, growWide, movImm]
  | load64 off =>
      obtain ⟨_, _, h1, _, _, _, rfl, rfl⟩ := gen_load64 hg; simp [instrSize]; omega
  | store64 off =>
      obtain ⟨_, _, h1, _, _, _, _, rfl, rfl⟩ := gen_store64 hg; simp [instrSize]
  | load8U off =>
      obtain ⟨_, _, h1, _, _, _, rfl, rfl⟩ := gen_load8U hg; simp [instrSize]; omega
  | store8 off =>
      obtain ⟨_, _, _, h1, _, _, _, _, rfl, rfl⟩ := gen_store8 hg; simp [instrSize]
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
      obtain ⟨-, -, hrl, rfl, fb, hl, -⟩ := gen_block hg
      have hs := ih _ σ a body is fb (by simp; omega) hl
      simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl] at hs
      constructor
      · simp only [instrSize]
        exact hs
      · simp only [instrSize, Option.map_some, List.length_append, List.length_reverse, hrl]
        congr 1
        omega
  | loop pa ra body pts rts =>
      obtain ⟨-, -, hrl, rfl, fb, hl, -⟩ := gen_loop hg
      have hs := ih _ σ a body is fb (by simp; omega) hl
      simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl] at hs
      constructor
      · simp only [instrSize]
        exact hs
      · simp only [instrSize, Option.map_some, List.length_append, List.length_reverse, hrl]
        congr 1
        omega
  | call k =>
      obtain ⟨target, ps, rs, hk, -, rfl, h, p, r, hσl, hpl, hrl0, hpb, -, -, -, spills,
        moves, res, reloads, g, rfl, hs, -, hm, -, hres, -, hrl, -, -⟩ := gen_call hg
      simp only [instrSize, sigOf, hk, Option.map_some, List.length_append, List.length_cons,
        List.length_nil, hs, hm, hres, hrl, hσl, hpl, hrl0, List.length_reverse, List.length_drop]
      constructor
      · omega
      · congr 1
        omega
  | iff pa ra thn els pts rts =>
      obtain ⟨-, -, hrl, hb1, -, rfl, ti, ta, ei, ea, f, g, ht, he, -, -, -, -, rfl⟩ := gen_iff hg
      have hst := ih _ _ _ thn ti ta (by simp; omega) ht
      have hse := ih _ _ _ els ei ea (by simp; omega) he
      simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl, List.length_tail] at hst hse
      constructor
      · simp only [instrSize, List.length_cons, List.length_append]
        omega
      · simp only [instrSize, Option.map_some, List.length_append, List.length_reverse, hrl,
          List.length_tail]
        congr 1
        omega
  | _ => simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hg

mutual

/-- The generated code of an instruction has the length that `instrSize` computes, and its end
is reachable when `instrSize` says so, at the height that it computes. -/
theorem genInstr_size {E : Env} : (ctl : List Ctl) → (σ : List ValueType) → (a : UInt64) →
    (inst : Instruction) → (is : List Instr) → (fin : Option (List ValueType)) →
    genInstr E ctl σ a inst = .ok (is, fin) →
    is.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σ.length inst).1 ∧
      fin.map List.length = (instrSize (sigOf E.callee) (ctl.map (·.arity)) σ.length inst).2
  | _, _, _, _, _, _, hg =>
      genInstr_size_of (fun ctl σ a p is fin _ hl => (genList_size ctl σ a p is fin hl).1) hg
termination_by _ _ _ inst _ _ _ => sizeOf inst
decreasing_by all_goals (try simp_wf); all_goals omega

/-- The generated code of an instruction list has the length that `listSize` computes, and its
end is reachable when `listSize` says so, at the height that it computes. -/
theorem genList_size {E : Env} : (ctl : List Ctl) → (σ : List ValueType) → (a : UInt64) →
    (p : List Instruction) → (is : List Instr) → (fin : Option (List ValueType)) →
    genList E ctl σ a p = .ok (is, fin) →
    is.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) σ.length p).1 ∧
      fin.map List.length = (listSize (sigOf E.callee) (ctl.map (·.arity)) σ.length p).2
  | ctl, σ, a, [], is, fin, hg => by
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      simp [listSize]
  | ctl, σ, a, i :: rest, is, fin, hg => by
      obtain ⟨c1, f1, h1, ⟨hf1, his, hfin⟩ | ⟨σ', c2, hf1, h2, his⟩⟩ := gen_cons hg
      · subst hf1 his hfin
        have s1 := genInstr_size ctl σ a i _ _ h1
        constructor
        · simp only [listSize, ← s1.2, Option.map_none]
          exact s1.1
        · simp only [listSize, ← s1.2, Option.map_none]
      · subst hf1 his
        have s1 := genInstr_size ctl σ a i _ _ h1
        have s2 := genList_size ctl σ' (after a c1.length) rest c2 fin h2
        constructor
        · simp only [listSize, ← s1.2, Option.map_some, List.length_append, s1.1, s2.1]
        · simp only [listSize, ← s1.2, Option.map_some, s2.2]
termination_by _ _ _ p _ _ _ => sizeOf p
decreasing_by all_goals (try simp_wf); all_goals omega

end

/-! ## Composition -/

theorem genInstr_base {E : Env} {ctl : List Ctl} {σ : List ValueType} {a : UInt64}
    {inst : Instruction} {is : List Instr} {σ' : List ValueType}
    (hg : genInstr E ctl σ a inst = .ok (is, some σ')) (hb : curBase ctl ≤ σ.length) :
    curBase ctl ≤ σ'.length := by
  cases inst with
  | localGet i => obtain ⟨_, _, _, _, he⟩ := gen_localGet hg; cases he; simp; omega
  | localSet i =>
      obtain ⟨_, _, h1, _, _, _, he⟩ := gen_localStore (.inl ⟨rfl, rfl⟩) hg; cases he; simp; omega
  | localTee i =>
      obtain ⟨_, _, h1, _, _, _, he⟩ := gen_localStore (.inr ⟨rfl, rfl⟩) hg; cases he; omega
  | constI64 w => obtain ⟨_, _, he⟩ := gen_const (.inl ⟨rfl, rfl⟩) hg; cases he; simp; omega
  | const c =>
      obtain ⟨_, _, he⟩ := gen_const (.inr (.inl ⟨c, rfl, rfl, rfl⟩)) hg; cases he; simp; omega
  | f64Const w =>
      obtain ⟨_, _, he⟩ := gen_const (.inr (.inr (.inl ⟨rfl, rfl⟩))) hg; cases he; simp; omega
  | f64Add | f64Sub | f64Mul | f64Div =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genFBin_ok hg
      cases he
      simp
      omega
  | f64Eq | f64Lt | f64Le =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genFCmp_ok hg
      cases he
      simp
      omega
  | f64Sqrt | f64Abs | f64ConvertI64U | i64TruncSatF64U | i64ReinterpretF64 | f64ReinterpretI64 =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genUn_ok hg
      cases he
      simp
      omega
  | f32Const c =>
      obtain ⟨_, _, he⟩ := gen_const (.inr (.inr (.inr ⟨c, rfl, rfl, rfl⟩))) hg; cases he; simp
      omega
  | f32Add | f32Sub | f32Mul | f32Div =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genFBin32_ok hg
      cases he
      simp
      omega
  | f32Eq | f32Lt | f32Le =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genFCmp32_ok hg
      cases he
      simp
      omega
  | f32Sqrt | f32Nearest | f32Abs | f32ConvertI64U | f32ConvertI32S | i64TruncSatF32U
  | i32TruncSatF32S | f32ReinterpretI32 | i32ReinterpretF32 =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genUn_ok hg
      cases he
      simp
      omega
  | eqI64 => obtain ⟨h1, _, _, he⟩ := gen_cmp (.inl rfl) hg; cases he; simp; omega
  | eq => obtain ⟨h1, _, _, he⟩ := gen_cmp (.inr rfl) hg; cases he; simp; omega
  | eqzI64 => obtain ⟨h1, _, _, he⟩ := gen_eqz (.inl rfl) hg; cases he; simp; omega
  | eqz => obtain ⟨h1, _, _, he⟩ := gen_eqz (.inr rfl) hg; cases he; simp; omega
  | neI64 | ltUI64 | leUI64 | geUI64 | ltSI64 | leSI64 =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genCmp_ok hg
      cases he
      simp
      omega
  | shrSI64 => obtain ⟨h1, _, _, he⟩ := gen_shrS hg; cases he; simp; omega
  | addI64 | subI64 | mulI64 | andI64 | and | orI64 | xorI64 | shlI64 | shrUI64 =>
      simp only [genInstr] at hg
      obtain ⟨h1, _, _, he⟩ := genBin_ok hg
      cases he
      simp
      omega
  | wrapI64 => obtain ⟨h1, _, _, he⟩ := gen_wrap hg; cases he; simp; omega
  | extendUI32 => obtain ⟨h1, _, he⟩ := gen_extend hg; cases he; simp; omega
  | remUI64 =>
      obtain ⟨h1, _, _, _, _, he⟩ := gen_divrem (.inl ⟨rfl, rfl⟩) hg; cases he; simp; omega
  | divUI64 =>
      obtain ⟨h1, _, _, _, _, he⟩ := gen_divrem (.inr ⟨rfl, rfl⟩) hg; cases he; simp; omega
  | unreachable => obtain ⟨_, _, _, he⟩ := gen_unreachable hg; cases he
  | globalGet i => obtain ⟨_, _, _, _, he⟩ := gen_globalGet hg; cases he; simp; omega
  | globalSet i => obtain ⟨_, h1, _, _, _, he⟩ := gen_globalSet hg; cases he; simp; omega
  | memorySize => obtain ⟨_, _, he⟩ := gen_memorySize hg; cases he; simp; omega
  | memoryGrow => obtain ⟨_, h1, _, _, _, he, -⟩ := gen_memoryGrow hg; cases he; omega
  | load64 off => obtain ⟨_, _, h1, _, _, _, _, he⟩ := gen_load64 hg; cases he; simp; omega
  | store64 off => obtain ⟨_, _, h1, _, _, _, _, _, he⟩ := gen_store64 hg; cases he; simp; omega
  | load8U off => obtain ⟨_, _, h1, _, _, _, _, he⟩ := gen_load8U hg; cases he; simp; omega
  | store8 off =>
      obtain ⟨_, _, _, h1, _, _, _, _, _, he⟩ := gen_store8 hg; cases he; simp; omega
  | br n => obtain ⟨_, _, _, he⟩ := gen_br hg; cases he
  | br_if n => obtain ⟨h1, _, he, _⟩ := gen_br_if hg; cases he; simp; omega
  | ret => obtain ⟨_, _, _, he⟩ := gen_ret hg; cases he
  | block pa ra body pts rts => obtain ⟨_, _, _, he, _⟩ := gen_block hg; cases he; simp; omega
  | loop pa ra body pts rts => obtain ⟨_, _, _, he, _⟩ := gen_loop hg; cases he; simp; omega
  | iff pa ra thn els pts rts =>
      obtain ⟨_, _, _, h1, _, he, _⟩ := gen_iff hg; cases he; simp; omega
  | call k =>
      obtain ⟨_, _, _, _, _, he, h, p, r, hσl, hpl, -, hpb, -⟩ := gen_call hg
      cases he
      simp
      omega
  | _ => simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hg

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
    (hlen : vs.length = t.base + t.arity) (hty : Typed t.types (vs.take t.arity)) :
    Kept t vs s := by
  have h26 := h.1
  refine ⟨by omega, by omega, fun j hj => ?_, hty⟩
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

theorem reach_pc {s : State} {p : UInt64} (h : s.pc = p) : Reach P code s { s with pc := p } := by
  subst h
  exact .refl _

/-- Talos's `if` either finds an `i32` on top of the stack or fails as invalid. -/
theorem execOne_iff_cases (f pa ra : Nat) (thn els : List Instruction)
    (pts rts : List ValueType) {α : Type} (m : Module) (st : Store α) (sl : Locals)
    (env : HostEnv α) :
    (∃ x vs, sl.values = .i32 x :: vs) ∨
      ∃ msg, execOne (f + 1) m st sl (.iff pa ra thn els pts rts) env = .Invalid msg := by
  cases hv : sl.values with
  | nil => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩
  | cons v vs =>
      cases v with
      | i32 x => exact .inl ⟨x, vs, rfl⟩
      | _ => exact .inr ⟨_, by simp only [execOne.eq_def, hv]; rfl⟩

/-! ## The simulation over a machine -/

namespace Machine

section General

variable {P code}
variable {α : Type} (M : Machine P code α)

/-- An outcome from a state that the machine reaches from `q` with SP, X18, the UART's output,
the memory outside the frame, and the registers below the innermost base unchanged, as an outcome
from `q`. -/
theorem Outcome.trans {E : Env} {ctl : List Ctl} {D : Nat} {fin : Option (List ValueType)}
    {endA : UInt64} {r : Continuation α} {q q1 : M.Q} (hctl : CtlOk ctl) (hr : M.Rch q q1)
    (hsp : (M.core q1).sp = (M.core q).sp) (hout : (M.core q1).io = (M.core q).io)
    (h18 : (M.core q1).x 18 = (M.core q).x 18)
    (hmf : MemFrame (M.core q).sp (E.locals + spillSlots) (M.core q) (M.core q1))
    (hfr : Frame (curBase ctl) (M.core q) (M.core q1)) (ho : M.Outcome E ctl D fin endA r q1) :
    M.Outcome E ctl D fin endA r q := by
  have hmf2 : ∀ q' : M.Q,
      MemFrame (M.core q1).sp (E.locals + spillSlots) (M.core q1) (M.core q') →
      MemFrame (M.core q).sp (E.locals + spillSlots) (M.core q) (M.core q') :=
    fun q' h b hb => by rw [h b (by rwa [hsp]), hmf b hb]
  rcases ho with ⟨hc, q', hr', hp, hout'⟩ | ho
  · exact .inl ⟨by rw [← hsp, ← h18]; exact hc, q', M.trans hr hr', hp, by rw [hout', hout]⟩
  refine .inr ?_
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf, q', hr', hp, hsp', hout', h18', hmf', hinv', hfr', hsr'⟩ := ho
      exact ⟨σ', hf, q', M.trans hr hr', hp, by rw [hsp', hsp], by rw [hout', hout],
        by rw [h18', h18], hmf2 q' hmf', hinv', fun k hk => by rw [hfr' k hk, hfr k hk], hsr'⟩
  | Break k st' sl' =>
      obtain ⟨t, ht, q', hr', hp, hsp', hout', h18', hmf', hloc, hcnt, hk, hfr', hsr'⟩ := ho
      exact ⟨t, ht, q', M.trans hr hr', hp, by rw [hsp', hsp], by rw [hout', hout],
        by rw [h18', h18], hmf2 q' hmf', hloc, hcnt, hk, fun j hj => by
          rw [hfr' j hj, hfr j (Nat.lt_of_lt_of_le hj (hctl.bases t (List.mem_of_getElem? ht)))],
        hsr'⟩
  | Return st' vs =>
      obtain ⟨t, ht, q', hr', hp, hsp', hout', h18', hmf', hk, hsr'⟩ := ho
      exact ⟨t, ht, q', M.trans hr hr', hp, by rw [hsp', hsp], by rw [hout', hout],
        by rw [h18', h18], hmf2 q' hmf', hk, hsr'⟩
  | Trap st' msg =>
      obtain ⟨q', hr', hout', hpc⟩ := ho
      exact ⟨q', M.trans hr hr', by rw [hout', hout], hpc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

/-- `ListSim` over the machine `M`, with Talos's run under `M.env`. -/
def ListSim (F : Nat) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt64) (p : List Instruction)
    (is : List Instr) (fin : Option (List ValueType)), genList E ctl σ a p = .ok (is, fin) →
    CodeAt code a is → curBase ctl ≤ σ.length → CtlOk ctl →
    ∀ (m : Module) (st : Store α) (sl : Locals) (q : M.Q),
      Inv P E.localTypes σ sl (M.core q) → M.SR E.cap E.globalTypes st q →
      m.memIs64 = false → (M.core q).pc = a → ∀ (need : Nat → Nat) (D : Nat),
      M.CallsOk F m E.callee E.toShared need → (∀ j ∈ callsIn p, need j ≤ D) →
      M.Outcome E ctl D fin (after a is.length) (Wasm.exec F m st sl p M.env) q

theorem prog_sim {F : Nat} (hI : ∀ inst, M.InstrSim F inst) : M.ListSim F := by
  intro E ctl σ a p
  induction p generalizing σ a with
  | nil =>
      intro is fin hg hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl hD
      obtain ⟨rfl, rfl⟩ := gen_nil hg
      rw [ProofKit.exec_nil]
      exact .inr ⟨σ, rfl, q, M.refl q, by simp [hpc, after_zero], rfl, rfl, rfl, fun _ _ => rfl,
        hinv, fun _ _ => rfl, hsr⟩
  | cons i rest ih =>
      intro is fin hg hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl hD
      have hDi : ∀ j ∈ callsOf i, need j ≤ D := fun j hj =>
        hD j (by simp only [callsIn]; exact List.mem_append_left _ hj)
      have hDr : ∀ j ∈ callsIn rest, need j ≤ D := fun j hj =>
        hD j (by simp only [callsIn]; exact List.mem_append_right _ hj)
      obtain ⟨c1, f1, h1, ⟨rfl, his, rfl⟩ | ⟨σ', c2, rfl, h2, rfl⟩⟩ := gen_cons hg
      · subst his
        have hi := hI i E ctl σ a _ none h1 hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl
          hDi
        rw [ProofKit.exec_cons]
        revert hi
        cases execOne F m st sl i M.env with
        | Fallthrough st' sl' =>
            intro hi
            rcases hi with hov | ⟨_, hn, _⟩
            · exact .inl hov
            · cases hn
        | _ => intro hi; exact hi
      · have hc := (CodeAt.append (code := code)).mp hcode
        have hi := hI i E ctl σ a c1 (some σ') h1 hc.1 hb hctl m st sl q hinv hsr h64 hpc need D
          hcl hDi
        rw [ProofKit.exec_cons]
        revert hi
        cases execOne F m st sl i M.env with
        | Fallthrough st' sl' =>
            intro hi
            rcases hi with hov | ⟨σ'', hn, q1, hr, hp, hsp, hout, h18, hmf, hinv1, hfr, hsr1⟩
            · exact .inl hov
            cases hn
            have ho := ih σ' (after a c1.length) c2 fin h2 hc.2 (genInstr_base h1 hb) hctl m st'
              sl' q1 hinv1 hsr1 h64 hp need D hcl hDr
            rw [after_after, ← List.length_append] at ho
            exact Outcome.trans M hctl hr hsp hout h18 hmf hfr ho
        | _ => intro hi; exact hi

/-- The outcome of a block or an `if` whose body, under the construct `t` and from `q1`, gives
`r`, where the machine reaches `q1` from `q` with only its program counter changed and the body's
end `endB` leads to `t.target`, over the stack `below` of the types `σb`. -/
theorem construct_outcome {E : Env} {ctl : List Ctl} {D : Nat} {r : Continuation α}
    {t : Ctl} {below : List Value} {σb σ0 : List ValueType} {sl0 : Locals} {q q1 : M.Q}
    {fb : Option (List ValueType)} {endB : UInt64} {ra : Nat} (hra : t.arity = ra)
    (hctl : CtlOk ctl) (hb : curBase ctl ≤ t.base) (hinv : Inv P E.localTypes σ0 sl0 (M.core q))
    (hbelow : StackRel (M.core q) below) (hbt : Typed σb below) (hlen : below.length = t.base)
    (hr1 : M.Rch q q1)
    (hsp1 : (M.core q1).sp = (M.core q).sp) (hout1 : (M.core q1).io = (M.core q).io)
    (hmem1 : (M.core q1).mem = (M.core q).mem) (hfr1 : ∀ r, (M.core q1).x r = (M.core q).x r)
    (hfb : ∀ x, fb = some x → x = t.types ++ σb)
    (hjump : ∀ s : State, s.pc = endB → Reach P code s { s with pc := t.target })
    (ho : M.Outcome E (t :: ctl) D fb endB r q1) :
    M.Outcome E ctl D (some (t.types ++ σb)) t.target (ProofKit.blockResult ra below r) q := by
  subst hra
  have hmf2 : ∀ q' : M.Q,
      MemFrame (M.core q1).sp (E.locals + spillSlots) (M.core q1) (M.core q') →
      MemFrame (M.core q).sp (E.locals + spillSlots) (M.core q) (M.core q') :=
    fun q' h b hb => by rw [h b (by rwa [hsp1]), hmem1]
  rcases ho with ⟨hc, q', hr', hp, hout'⟩ | ho
  · exact .inl ⟨by rw [← hsp1, ← hfr1 18]; exact hc, q', M.trans hr1 hr', hp,
      by rw [hout', hout1]⟩
  refine .inr ?_
  cases r with
  | Fallthrough st' sl' =>
      obtain ⟨σ', hf, q', hr', hp, hsp', hout', h18', hmf', hinv', hfr', hsr'⟩ := ho
      have hσ' := hfb σ' hf
      obtain ⟨q'', hq'', hc'', hsr''⟩ := M.lift_pc hsr' (hjump (M.core q') hp)
      have hfr2 : Frame t.base (M.core q) { M.core q' with pc := t.target } := fun k hk => by
        show (M.core q').x (regOf k) = (M.core q).x (regOf k)
        rw [hfr' k hk, hfr1]
      have hty' := hinv'.types
      rw [hσ'] at hty'
      have htk : Typed t.types (sl'.values.take t.arity) := by
        have := hty'.take t.types.length
        rwa [List.take_left' rfl] at this
      have hl' : sl'.values.length = t.base + t.arity := by
        rw [← hty'.length, List.length_append, hbt.length, hlen]
        show t.types.length + t.base = t.base + t.types.length
        omega
      refine ⟨_, rfl, q'', M.trans hr1 (M.trans hr' hq''), by rw [hc''],
        by rw [hc'']; show (M.core q').sp = (M.core q).sp; rw [hsp', hsp1],
        by rw [hc'']; show (M.core q').io = (M.core q).io; rw [hout', hout1],
        by rw [hc'']; show (M.core q').x 18 = (M.core q).x 18; rw [h18', hfr1],
        by rw [hc'']; exact hmf2 _ hmf', ?_,
        fun k hk => by rw [hc'']; exact hfr2 k (Nat.lt_of_lt_of_le hk hb), hsr''⟩
      rw [hc'']
      exact ⟨StackRel.of_kept (StackRel.kept (hinv'.stack.congr fun _ _ => rfl) hl' htk)
          hbelow hlen hfr2, hinv'.locals.congr rfl rfl, hinv'.count, hinv'.frame.congr rfl rfl,
        htk.append hbt, hinv'.ltypes⟩
  | Break k st' sl' =>
      obtain ⟨t', ht', q', hr', hp, hsp', hout', h18', hmf', hloc, hcnt, hk, hfr', hsr'⟩ := ho
      have h182 : (M.core q').x 18 = (M.core q).x 18 := by rw [h18', hfr1]
      cases k with
      | zero =>
          have ht0 : t' = t := by simpa using ht'.symm
          rw [ht0] at hp hk hfr'
          have hfr2 : Frame t.base (M.core q) (M.core q') := fun k hk => by rw [hfr' k hk, hfr1]
          have hsp2 : (M.core q').sp = (M.core q).sp := by rw [hsp', hsp1]
          refine ⟨_, rfl, q', M.trans hr1 hr', hp, hsp2, by rw [hout', hout1], h182,
            hmf2 _ hmf', ?_, fun k hk => hfr2 k (Nat.lt_of_lt_of_le hk hb), hsr'⟩
          exact ⟨StackRel.of_kept hk hbelow hlen hfr2, hloc, hcnt.length.symm,
            hinv.frame.congr hsp2 h182, hk.types.append hbt, hcnt⟩
      | succ k =>
          refine ⟨t', ht', q', M.trans hr1 hr', hp, by rw [hsp', hsp1], by rw [hout', hout1],
            h182, hmf2 _ hmf', hloc, hcnt, hk, fun j hj => by rw [hfr' j hj, hfr1], hsr'⟩
  | Return st' vs =>
      obtain ⟨t', ht', q', hr', hp, hsp', hout', h18', hmf', hk, hsr'⟩ := ho
      exact ⟨t', by rwa [getLast?_push hctl.nonempty] at ht', q', M.trans hr1 hr', hp,
        by rw [hsp', hsp1], by rw [hout', hout1], by rw [h18', hfr1], hmf2 _ hmf', hk, hsr'⟩
  | Trap st' msg =>
      obtain ⟨q', hr', hout', hpc⟩ := ho
      exact ⟨q', M.trans hr1 hr', by rw [hout', hout1], hpc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => exact ho.elim
  | Throwing _ _ _ _ => exact ho.elim

theorem sim_block {f : Nat} (hP : M.ListSim f) (pa ra : Nat) (body : List Instruction)
    (pts rts : List ValueType) : M.InstrSim (f + 1) (.block pa ra body pts rts) := by
  intro E ctl σ a is fin hgen hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl hD
  obtain ⟨rfl, hra, hrl, rfl, fb, hl, hfb⟩ := gen_block hgen
  have hn := (genList_size _ σ a body is fb hl).1
  simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl] at hn
  let t : Ctl := { target := after a is.length, types := rts.reverse, base := σ.length }
  have hl' : genList E (t :: ctl) σ a body = .ok (is, fb) := by
    show genList E ({ target := after a is.length, types := rts.reverse, base := σ.length } ::
      ctl) σ a body = _
    rw [hn]
    exact hl
  have ho := hP E (t :: ctl) σ a body is fb hl' hcode (Nat.le_refl _) (hctl.push hb) m st sl q
    hinv hsr h64 hpc need D (hcl.mono (by omega))
    fun j hj => hD j (by simpa [callsOf] using hj)
  rw [ProofKit.execOne_block]
  exact construct_outcome M (t := t) (by simp [t, Ctl.arity, hrl]) hctl hb hinv hinv.stack
    hinv.types hinv.len (M.refl q) rfl rfl rfl (fun _ => rfl) hfb
    (fun _ hs => reach_pc P code hs) ho

theorem sim_loop {F : Nat} (hP : ∀ g < F, M.ListSim g) (pa ra : Nat)
    (body : List Instruction) (pts rts : List ValueType) :
    M.InstrSim F (.loop pa ra body pts rts) := by
  suffices key : ∀ g, g ≤ F → M.InstrSim g (.loop pa ra body pts rts) from
    key F (Nat.le_refl _)
  intro g
  induction g with
  | zero =>
      intro _ E ctl σ a is fin hgen hcode hb hctl m st sl q hinv _ _ hpc _ _ _ _
      rw [ProofKit.execOne_zero]
      exact .inr trivial
  | succ f ih =>
      intro hf E ctl σ a is fin hgen hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl hD
      obtain ⟨rfl, hra, hrl, rfl, fb, hl, hfb⟩ := gen_loop hgen
      let t : Ctl := { target := a, types := [], base := σ.length }
      have ho := hP f (by omega) E (t :: ctl) σ a body is fb hl hcode (Nat.le_refl _)
        (hctl.push hb) m st sl q hinv hsr h64 hpc need D (hcl.mono (by omega))
        fun j hj => hD j (by simpa [callsOf] using hj)
      rw [execOne_loop_succ f m st sl M.env 0 ra body pts rts]
      revert ho
      cases Wasm.exec f m st sl body M.env with
      | Fallthrough st' sl' =>
          intro ho
          let t2 : Ctl := { target := after a is.length, types := rts.reverse, base := σ.length }
          exact construct_outcome M (t := t2) (r := .Fallthrough st' sl')
            (by simp [t2, Ctl.arity, hrl]) hctl hb hinv hinv.stack hinv.types hinv.len (M.refl q)
            rfl rfl rfl (fun _ => rfl) hfb (fun _ hs => reach_pc P code hs) ho
      | Break k st' sl' =>
          intro ho
          rcases ho with hov | ⟨t', ht', q', hr, hp, hsp, hout, h18, hmf, hloc, hcnt, hk, hfr,
            hsr'⟩
          · exact .inl hov
          cases k with
          | zero =>
              have ht0 : t' = t := by simpa using ht'.symm
              rw [ht0] at hp hfr
              have hfr' : Frame σ.length (M.core q) (M.core q') := hfr
              have hh := hinv.len
              have hinv2 : Inv P E.localTypes σ
                  { sl' with values := sl'.values.take 0 ++ sl.values.drop 0 } (M.core q') :=
                ⟨hinv.stack.congr fun k hk => hfr' k (by omega), hloc, hcnt.length.symm,
                  hinv.frame.congr hsp h18, hinv.types, hcnt⟩
              exact Outcome.trans M hctl hr hsp hout h18 hmf
                (fun k hk => hfr' k (Nat.lt_of_lt_of_le hk hb))
                (ih (by omega) E ctl σ a is _ hgen hcode hb hctl m st' _ q' hinv2 hsr' h64 hp
                  need D (hcl.mono (by omega)) hD)
          | succ k =>
              exact .inr ⟨t', ht', q', hr, hp, hsp, hout, h18, hmf, hloc, hcnt, hk, hfr, hsr'⟩
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

theorem sim_iff {f : Nat} (hP : M.ListSim f) (pa ra : Nat) (thn els : List Instruction)
    (pts rts : List ValueType) : M.InstrSim (f + 1) (.iff pa ra thn els pts rts) := by
  intro E ctl σ a is fin hgen hcode hb hctl m st sl q hinv hsr h64 hpc need D hcl hD
  have hDt : ∀ j ∈ callsIn thn, need j ≤ D := fun j hj =>
    hD j (by simp only [callsOf]; exact List.mem_append_left _ hj)
  have hDe : ∀ j ∈ callsIn els, need j ≤ D := fun j hj =>
    hD j (by simp only [callsOf]; exact List.mem_append_right _ hj)
  obtain ⟨rfl, hra, hrl, hhb, hlt, rfl, ti, ta, ei, ea, g1, g2, hthn, hels, hta, hea, hg1, hg2,
    his⟩ := gen_iff hgen
  have hh := hinv.len
  have hst := (genList_size _ _ _ thn ti ta hthn).1
  have hse := (genList_size _ _ _ els ei ea hels).1
  simp only [List.map_cons, Ctl.arity_mk, List.length_reverse, hrl, List.length_tail] at hst hse
  have eB : after a
      (1 + (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (σ.length - 1) thn).1) =
      after (after a 1) ti.length := by
    rw [← hst, after_after]
  have eEnd : after (after (after a
      (1 + (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (σ.length - 1) thn).1)) 1)
      (listSize (sigOf E.callee) (ra :: ctl.map (·.arity)) (σ.length - 1) els).1 =
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
  rcases execOne_iff_cases f 0 ra thn els pts rts m st sl M.env with ⟨x, vs, hv⟩ | ⟨msg, hex⟩
  · rw [ProofKit.execOne_iff m st sl M.env f 0 ra thn els pts rts x vs hv, List.drop_zero]
    have hvl : vs.length = σ.length - 1 := by rw [hv] at hh; simp at hh; omega
    have hst0 := hinv.stack
    rw [hv] at hst0
    have hty := hinv.types
    rw [hv] at hty
    have hx : (M.core q).x (regOf (σ.length - 1)) = x.toUInt64 := by
      have := hst0.top; rw [hvl] at this; exact this
    let t : Ctl := { target := after a is.length, types := rts.reverse, base := σ.length - 1 }
    have hctl' : CtlOk (t :: ctl) := hctl.push (show curBase ctl ≤ σ.length - 1 by omega)
    have hbase : curBase (t :: ctl) ≤ σ.tail.length := by
      show σ.length - 1 ≤ σ.tail.length
      rw [List.length_tail]
      exact Nat.le_refl _
    have hcz : code (M.core q).pc = some (encode (.cbz (regOf (σ.length - 1)) g1)) := by
      rw [hpc]; exact c0
    by_cases hx0 : x = 0
    · rw [ite_eq_right (c := x ≠ 0) (fun hne => hne hx0)]
      have hreg : (M.core q).x (regOf (σ.length - 1)) = 0 := by rw [hx, hx0]; rfl
      obtain ⟨q1, hq1, hc1', hsr1⟩ := M.lift_pc hsr (cbz_taken P code hcz hpc hg1 hreg)
      have ho := hP E (t :: ctl) σ.tail _ els ei ea hels cE hbase hctl' m st
        { sl with values := vs } q1 (by rw [hc1']; exact Inv.pop P hinv hv _) hsr1 h64
        (by rw [hc1']) need D (hcl.mono (by omega)) hDe
      exact construct_outcome M (t := t) (by simp [t, Ctl.arity, hrl]) hctl
        (show curBase ctl ≤ σ.length - 1 by omega) hinv hst0.pop hty.tail hvl hq1
        (by rw [hc1']) (by rw [hc1']) (by rw [hc1']) (fun _ => by rw [hc1']; rfl) hea
        (fun _ hs => reach_pc P code (hs.trans eEndE)) ho
    · rw [ite_eq_left hx0]
      have hreg : (M.core q).x (regOf (σ.length - 1)) ≠ 0 := by
        rw [hx]
        exact fun e => hx0 (UInt32.toUInt64_inj.mp (by rw [e]; rfl))
      obtain ⟨q1, hq1, hc1', hsr1⟩ :=
        M.lift_pc hsr (reach_exec P code hcz (cbz_next P hreg) (.refl _))
      have ho := hP E (t :: ctl) σ.tail (after a 1) thn ti ta hthn hc1.1 hbase hctl'
        m st { sl with values := vs } q1 (by rw [hc1']; exact Inv.pop P hinv hv _) hsr1 h64
        (by rw [hc1']; simp [hpc, after]) need D (hcl.mono (by omega)) hDt
      have hjump : ∀ s : State, s.pc = after (after a 1) ti.length →
          Reach P code s { s with pc := t.target } := by
        intro s hs
        refine reach_exec P code (by rw [hs]; exact cB) ?_ (.refl _)
        show some { s with pc := s.pc + sext 26 g2.val * 4 } =
          some { s with pc := after a is.length }
        rw [hs, bField_target hg2]
      exact construct_outcome M (t := t) (by simp [t, Ctl.arity, hrl]) hctl
        (show curBase ctl ≤ σ.length - 1 by omega) hinv hst0.pop hty.tail hvl hq1
        (by rw [hc1']) (by rw [hc1']) (by rw [hc1']) (fun _ => by rw [hc1']; rfl) hta hjump ho
  · rw [hex]
    exact .inr trivial

theorem sim_zero (inst : Instruction) : M.InstrSim 0 inst := by
  intro E ctl σ a is fin _ _ _ _ m st sl q _ _ _ _ _ _ _ _
  rw [ProofKit.execOne_zero]
  exact .inr trivial

/-- The simulation of every instruction at fuel `F` over the machine `M`, given that of
instruction lists at every fuel below `F`: the constructs and calls by their proofs over `M`, and
the other forms by their proofs in the program's model and `InstrSim.of_leaf`.  The generator
rejects the forms outside this case analysis. -/
theorem instr_sim {F : Nat} (hP : ∀ g < F, M.ListSim g) (inst : Instruction) :
    M.InstrSim F inst := by
  cases inst
  case localGet i => exact InstrSim.of_leaf M (sim_localGet P code F i) (by leaf_tac)
  case localSet i => exact InstrSim.of_leaf M (sim_localSet P code F i) (by leaf_tac)
  case localTee i => exact InstrSim.of_leaf M (sim_localTee P code F i) (by leaf_tac)
  case constI64 w => exact InstrSim.of_leaf M (sim_constI64 P code F w) (by leaf_tac)
  case const c => exact InstrSim.of_leaf M (sim_const P code F c) (by leaf_tac)
  case eqI64 => exact InstrSim.of_leaf M (sim_eqI64 P code F) (by leaf_tac)
  case eq => exact InstrSim.of_leaf M (sim_eq P code F) (by leaf_tac)
  case eqzI64 => exact InstrSim.of_leaf M (sim_eqzI64 P code F) (by leaf_tac)
  case eqz => exact InstrSim.of_leaf M (sim_eqz P code F) (by leaf_tac)
  case extendUI32 => exact InstrSim.of_leaf M (sim_extendUI32 P code F) (by leaf_tac)
  case neI64 => exact InstrSim.of_leaf M (sim_neI64 P code F) (by leaf_tac)
  case ltUI64 => exact InstrSim.of_leaf M (sim_ltUI64 P code F) (by leaf_tac)
  case leUI64 => exact InstrSim.of_leaf M (sim_leUI64 P code F) (by leaf_tac)
  case geUI64 => exact InstrSim.of_leaf M (sim_geUI64 P code F) (by leaf_tac)
  case ltSI64 => exact InstrSim.of_leaf M (sim_ltSI64 P code F) (by leaf_tac)
  case leSI64 => exact InstrSim.of_leaf M (sim_leSI64 P code F) (by leaf_tac)
  case addI64 => exact InstrSim.of_leaf M (sim_addI64 P code F) (by leaf_tac)
  case subI64 => exact InstrSim.of_leaf M (sim_subI64 P code F) (by leaf_tac)
  case mulI64 => exact InstrSim.of_leaf M (sim_mulI64 P code F) (by leaf_tac)
  case andI64 => exact InstrSim.of_leaf M (sim_andI64 P code F) (by leaf_tac)
  case and => exact InstrSim.of_leaf M (sim_and P code F) (by leaf_tac)
  case orI64 => exact InstrSim.of_leaf M (sim_orI64 P code F) (by leaf_tac)
  case xorI64 => exact InstrSim.of_leaf M (sim_xorI64 P code F) (by leaf_tac)
  case shlI64 => exact InstrSim.of_leaf M (sim_shlI64 P code F) (by leaf_tac)
  case shrUI64 => exact InstrSim.of_leaf M (sim_shrUI64 P code F) (by leaf_tac)
  case shrSI64 => exact InstrSim.of_leaf M (sim_shrSI64 P code F) (by leaf_tac)
  case wrapI64 => exact InstrSim.of_leaf M (sim_wrapI64 P code F) (by leaf_tac)
  case f64Const w => exact InstrSim.of_leaf M (sim_f64Const P code F w) (by leaf_tac)
  case f64Add => exact InstrSim.of_leaf M (sim_f64Add P code F) (by leaf_tac)
  case f64Sub => exact InstrSim.of_leaf M (sim_f64Sub P code F) (by leaf_tac)
  case f64Mul => exact InstrSim.of_leaf M (sim_f64Mul P code F) (by leaf_tac)
  case f64Div => exact InstrSim.of_leaf M (sim_f64Div P code F) (by leaf_tac)
  case f64Eq => exact InstrSim.of_leaf M (sim_f64Eq P code F) (by leaf_tac)
  case f64Lt => exact InstrSim.of_leaf M (sim_f64Lt P code F) (by leaf_tac)
  case f64Le => exact InstrSim.of_leaf M (sim_f64Le P code F) (by leaf_tac)
  case f64Sqrt => exact InstrSim.of_leaf M (sim_f64Sqrt P code F) (by leaf_tac)
  case f64Abs => exact InstrSim.of_leaf M (sim_f64Abs P code F) (by leaf_tac)
  case f64ConvertI64U => exact InstrSim.of_leaf M (sim_f64ConvertI64U P code F) (by leaf_tac)
  case i64TruncSatF64U => exact InstrSim.of_leaf M (sim_i64TruncSatF64U P code F) (by leaf_tac)
  case i64ReinterpretF64 =>
    exact InstrSim.of_leaf M (sim_i64ReinterpretF64 P code F) (by leaf_tac)
  case f64ReinterpretI64 =>
    exact InstrSim.of_leaf M (sim_f64ReinterpretI64 P code F) (by leaf_tac)
  case f32Const c => exact InstrSim.of_leaf M (sim_f32Const P code F c) (by leaf_tac)
  case f32Add => exact InstrSim.of_leaf M (sim_f32Add P code F) (by leaf_tac)
  case f32Sub => exact InstrSim.of_leaf M (sim_f32Sub P code F) (by leaf_tac)
  case f32Mul => exact InstrSim.of_leaf M (sim_f32Mul P code F) (by leaf_tac)
  case f32Div => exact InstrSim.of_leaf M (sim_f32Div P code F) (by leaf_tac)
  case f32Eq => exact InstrSim.of_leaf M (sim_f32Eq P code F) (by leaf_tac)
  case f32Lt => exact InstrSim.of_leaf M (sim_f32Lt P code F) (by leaf_tac)
  case f32Le => exact InstrSim.of_leaf M (sim_f32Le P code F) (by leaf_tac)
  case f32Sqrt => exact InstrSim.of_leaf M (sim_f32Sqrt P code F) (by leaf_tac)
  case f32Nearest => exact InstrSim.of_leaf M (sim_f32Nearest P code F) (by leaf_tac)
  case f32Abs => exact InstrSim.of_leaf M (sim_f32Abs P code F) (by leaf_tac)
  case f32ConvertI64U => exact InstrSim.of_leaf M (sim_f32ConvertI64U P code F) (by leaf_tac)
  case f32ConvertI32S => exact InstrSim.of_leaf M (sim_f32ConvertI32S P code F) (by leaf_tac)
  case i64TruncSatF32U => exact InstrSim.of_leaf M (sim_i64TruncSatF32U P code F) (by leaf_tac)
  case i32TruncSatF32S => exact InstrSim.of_leaf M (sim_i32TruncSatF32S P code F) (by leaf_tac)
  case f32ReinterpretI32 =>
    exact InstrSim.of_leaf M (sim_f32ReinterpretI32 P code F) (by leaf_tac)
  case i32ReinterpretF32 =>
    exact InstrSim.of_leaf M (sim_i32ReinterpretF32 P code F) (by leaf_tac)
  case remUI64 => exact InstrSim.of_leaf M (sim_remUI64 P code F) (by leaf_tac)
  case divUI64 => exact InstrSim.of_leaf M (sim_divUI64 P code F) (by leaf_tac)
  case unreachable => exact InstrSim.of_leaf M (sim_unreachable P code F) (by leaf_tac)
  case globalGet i => exact InstrSim.of_leaf M (sim_globalGet P code F i) (by leaf_tac)
  case globalSet i => exact InstrSim.of_leaf M (sim_globalSet P code F i) (by leaf_tac)
  case memorySize => exact InstrSim.of_leaf M (sim_memorySize P code F) (by leaf_tac)
  case memoryGrow => exact InstrSim.of_leaf M (sim_memoryGrow P code F) (by leaf_tac)
  case load64 off => exact InstrSim.of_leaf M (sim_load64 P code F off) (by leaf_tac)
  case store64 off => exact InstrSim.of_leaf M (sim_store64 P code F off) (by leaf_tac)
  case load8U off => exact InstrSim.of_leaf M (sim_load8U P code F off) (by leaf_tac)
  case store8 off => exact InstrSim.of_leaf M (sim_store8 P code F off) (by leaf_tac)
  case br n => exact InstrSim.of_leaf M (sim_br P code F n) (by leaf_tac)
  case br_if n => exact InstrSim.of_leaf M (sim_br_if P code F n) (by leaf_tac)
  case ret => exact InstrSim.of_leaf M (sim_ret P code F) (by leaf_tac)
  case block pa ra body pts rts =>
    cases F with
    | zero => exact sim_zero M _
    | succ f => exact sim_block M (hP f (by omega)) pa ra body pts rts
  case loop pa ra body pts rts => exact sim_loop M hP pa ra body pts rts
  case iff pa ra thn els pts rts =>
    cases F with
    | zero => exact sim_zero M _
    | succ f => exact sim_iff M (hP f (by omega)) pa ra thn els pts rts
  case call k =>
    cases F with
    | zero => exact sim_zero M _
    | succ f => exact sim_call M f k
  all_goals
    intro E ctl h a is fin hgen
    simp [genInstr, throw, throwThe, MonadExceptOf.throw] at hgen

/-- The simulation of instruction lists at every fuel over the machine `M`. -/
theorem list_sim (F : Nat) : M.ListSim F := by
  induction F using Nat.strongRecOn with
  | _ F ih => exact prog_sim M (instr_sim M ih)

end General

end Machine

/-! ## At the bare machine

The theorems of the program's model follow from those over a machine at `bare P code α` for
every `α`.  Since `Machine.list_sim` holds with no premise, the theorems below that assume the
simulation of lists or instructions at other fuels hold without it. -/

/-- An outcome from a state that the machine reaches from `ms` with SP, X18, the UART's output,
the memory outside the frame, and the registers below the innermost base unchanged, as an outcome
from `ms`. -/
theorem Outcome.trans {E : Env} {ctl : List Ctl} {D : Nat} {fin : Option (List ValueType)}
    {endA : UInt64} {α : Type}
    {r : Continuation α} {ms ms1 : State} (hctl : CtlOk ctl) (hr : Reach P code ms ms1)
    (hsp : ms1.sp = ms.sp) (hout : ms1.io = ms.io) (h18 : ms1.x 18 = ms.x 18)
    (hmf : MemFrame ms.sp (E.locals + spillSlots) ms ms1)
    (hfr : Frame (curBase ctl) ms ms1) (ho : Outcome P code E ctl D fin endA r ms1) :
    Outcome P code E ctl D fin endA r ms :=
  Machine.Outcome.trans (bare P code α) (q := ms) (q1 := ms1) hctl hr hsp hout h18 hmf hfr ho

/-- The simulation of instruction lists at fuel `F`, in which an overflow of the stack occurs
only when fewer than `D` bytes lie between the stack's limit and SP, for any `D` at or above
`need j` for each function `j` that the list calls. -/
def ListSim (F : Nat) : Prop :=
  ∀ (E : Env) (ctl : List Ctl) (σ : List ValueType) (a : UInt64) (p : List Instruction)
    (is : List Instr) (fin : Option (List ValueType)), genList E ctl σ a p = .ok (is, fin) →
    CodeAt code a is → curBase ctl ≤ σ.length → CtlOk ctl →
    ∀ {α : Type} (m : Module) (st : Store α) (sl : Locals) (ms : State),
      Inv P E.localTypes σ sl ms → StoreRel P E.cap E.globalTypes st ms → m.memIs64 = false →
      ms.pc = a → ∀ (need : Nat → Nat) (D : Nat), CallsOk P code F m E.callee E.toShared need →
      (∀ j ∈ callsIn p, need j ≤ D) →
      Outcome P code E ctl D fin (after a is.length) (Wasm.exec F m st sl p) ms

/-- `ListSim` follows from its form at the bare machine of every host state. -/
theorem ListSim.of_bare {F : Nat} (h : ∀ α, (bare P code α).ListSim F) : ListSim P code F :=
  fun E ctl σ a p is fin hg hc hb hctl α m st sl ms hinv hsr h64 hpc need D hcl hD =>
    h α E ctl σ a p is fin hg hc hb hctl m st sl ms hinv hsr h64 hpc need D
      ((CallsOk.iff_bare P code _ _ _ _ _).mp hcl α) hD

/-- The simulation of instruction lists at every fuel. -/
theorem list_sim (F : Nat) : ListSim P code F :=
  ListSim.of_bare P code fun α => (bare P code α).list_sim F

theorem prog_sim {F : Nat} (_hI : ∀ inst, InstrSim P code F inst) : ListSim P code F :=
  list_sim P code F

/-- The outcome of a block or an `if` whose body, under the construct `t` and from `ms1`, gives
`r`, where the machine reaches `ms1` from `ms` with only its program counter changed and the
body's end `endB` leads to `t.target`, over the stack `below` of the types `σb`. -/
theorem construct_outcome {E : Env} {ctl : List Ctl} {D : Nat} {α : Type} {r : Continuation α}
    {t : Ctl} {below : List Value} {σb σ0 : List ValueType} {sl0 : Locals} {ms ms1 : State}
    {fb : Option (List ValueType)} {endB : UInt64} {ra : Nat} (hra : t.arity = ra)
    (hctl : CtlOk ctl) (hb : curBase ctl ≤ t.base) (hinv : Inv P E.localTypes σ0 sl0 ms)
    (hbelow : StackRel ms below) (hbt : Typed σb below) (hlen : below.length = t.base)
    (hr1 : Reach P code ms ms1)
    (hsp1 : ms1.sp = ms.sp) (hout1 : ms1.io = ms.io) (hmem1 : ms1.mem = ms.mem)
    (hfr1 : ∀ q, ms1.x q = ms.x q) (hfb : ∀ x, fb = some x → x = t.types ++ σb)
    (hjump : ∀ s : State, s.pc = endB → Reach P code s { s with pc := t.target })
    (ho : Outcome P code E (t :: ctl) D fb endB r ms1) :
    Outcome P code E ctl D (some (t.types ++ σb)) t.target
      (ProofKit.blockResult ra below r) ms :=
  Machine.construct_outcome (bare P code α) (q := ms) (q1 := ms1) hra hctl hb hinv hbelow hbt
    hlen hr1 hsp1 hout1 hmem1 hfr1 hfb hjump ho

theorem sim_block {f : Nat} (_hP : ListSim P code f) (pa ra : Nat) (body : List Instruction)
    (pts rts : List ValueType) : InstrSim P code (f + 1) (.block pa ra body pts rts) :=
  InstrSim.of_bare P code fun α =>
    (bare P code α).sim_block ((bare P code α).list_sim f) pa ra body pts rts

theorem sim_loop {F : Nat} (_hP : ∀ g < F, ListSim P code g) (pa ra : Nat)
    (body : List Instruction) (pts rts : List ValueType) :
    InstrSim P code F (.loop pa ra body pts rts) :=
  InstrSim.of_bare P code fun α =>
    (bare P code α).sim_loop (fun g _ => (bare P code α).list_sim g) pa ra body pts rts

theorem exec_iff_cases (f pa ra : Nat) (thn els : List Instruction) (pts rts : List ValueType)
    {α : Type} (m : Module) (st : Store α) (sl : Locals) :
    (∃ x vs, sl.values = .i32 x :: vs) ∨
      ∃ msg, execOne (f + 1) m st sl (.iff pa ra thn els pts rts) = .Invalid msg :=
  execOne_iff_cases f pa ra thn els pts rts m st sl {}

theorem sim_iff {f : Nat} (_hP : ListSim P code f) (pa ra : Nat) (thn els : List Instruction)
    (pts rts : List ValueType) : InstrSim P code (f + 1) (.iff pa ra thn els pts rts) :=
  InstrSim.of_bare P code fun α =>
    (bare P code α).sim_iff ((bare P code α).list_sim f) pa ra thn els pts rts

/-! ## Every instruction and list -/

theorem sim_zero (inst : Instruction) : InstrSim P code 0 inst := by
  intro E ctl σ a is fin _ _ _ _ α m st sl ms _ _ _ _ _ _ _ _
  rw [ProofKit.execOne_zero]
  exact .inr trivial

/-- The simulation of every instruction at fuel `F`, given that of instruction lists at every
fuel below `F`.  The generator rejects the forms outside this case analysis. -/
theorem instr_sim {F : Nat} (_hP : ∀ g < F, ListSim P code g) (inst : Instruction) :
    InstrSim P code F inst :=
  InstrSim.of_bare P code fun α =>
    (bare P code α).instr_sim (fun g _ => (bare P code α).list_sim g) inst

end LeanExe.A64
