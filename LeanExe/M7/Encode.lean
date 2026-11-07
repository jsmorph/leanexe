import LeanExe.M7.Machine

/-!
The encoder of the model's instruction forms and the lemmas that tie it to the decoder.
`decode_encode` states that the decoder reads every encoded instruction back as itself, followed
by any halfwords, and `decode_sound` that every instruction the decoder reads from halfwords is
the encoding of what it returns, so the decoder accepts exactly the bit patterns that the encoder
writes.  `encodeNat_injective`, which the first lemma uses, states that no two instructions share
an encoding.  Each proof reads fields back with `omega` and uses no bit-vector decision
procedure.  GNU `as` assembles sample instructions of every form to the same halfwords.
-/

namespace LeanExe.M7

/-- The halfwords of the instruction `i`, the first at the lower address: two when the first
starts a 32-bit instruction, and one otherwise. -/
def encode (i : Instr) : List UInt16 :=
  if wide (encodeNat i).1 then [UInt16.ofNat (encodeNat i).1, UInt16.ofNat (encodeNat i).2]
  else [UInt16.ofNat (encodeNat i).1]

theorem encodeNat_lt (i : Instr) : (encodeNat i).1 < 65536 ∧ (encodeNat i).2 < 65536 := by
  cases i <;> simp only [encodeNat] <;> omega

/-- Every form but `BX LR` is 32 bits wide. -/
theorem wide_encodeNat (i : Instr) : wide (encodeNat i).1 ↔ i ≠ .bxLr := by
  cases i <;> simp only [wide, encodeNat, ne_eq, reduceCtorEq, not_false_eq_true, iff_true,
    not_true_eq_false, iff_false, Nat.not_le] <;> omega

theorem length_encode_of_ne {i : Instr} (h : i ≠ .bxLr) : (encode i).length = 2 := by
  simp only [encode, (wide_encodeNat i).mpr h, ↓reduceIte, List.length_cons, List.length_nil]

theorem encode_bxLr : encode .bxLr = [0x4770] := rfl

/-- Proves the goal `a = b` from `encodeNat a = encodeNat b` in context, for constructors `a` and
`b`: it splits the equation of pairs, rewrites an equation of different constructors to `False`
and one of the same constructor to equations of the fields' values, and decides the result with
`omega`, which knows the bounds of `Fin` fields, or with `rfl` for a form without fields. -/
syntax "injective_tac" : tactic
macro_rules
  | `(tactic| injective_tac) => `(tactic| (
      intro h
      simp only [encodeNat, Prod.mk.injEq] at h
      all_goals try simp only [reduceCtorEq, Instr.addReg.injEq, Instr.adcReg.injEq,
        Instr.subReg.injEq, Instr.sbcReg.injEq, Instr.andReg.injEq, Instr.orrReg.injEq,
        Instr.eorReg.injEq, Instr.cmpReg.injEq, Instr.lslReg.injEq, Instr.lsrReg.injEq,
        Instr.lslImm.injEq, Instr.lsrImm.injEq, Instr.subImm.injEq, Instr.andImm.injEq,
        Instr.eorImm.injEq, Instr.cmpImm.injEq, Instr.movImm.injEq, Instr.movw.injEq,
        Instr.movt.injEq, Instr.addwSp.injEq, Instr.subwSp.injEq, Instr.addwSpSp.injEq,
        Instr.subwSpSp.injEq, Instr.clz.injEq, Instr.umull.injEq, Instr.mla.injEq, Instr.mls.injEq,
        Instr.udiv.injEq, Instr.ldr.injEq, Instr.str.injEq, Instr.ldrSp.injEq, Instr.strSp.injEq,
        Instr.ldrLr.injEq, Instr.strLr.injEq, Instr.bcond.injEq, Instr.b.injEq, Instr.bl.injEq,
        Fin.ext_iff, and_true]
      all_goals first | rfl | omega))

set_option maxHeartbeats 4000000 in
/-- No two instructions share an encoding.  The proof compares every pair of forms, so its cost
grows with the square of the number of forms, beyond the default budget of heartbeats. -/
theorem encodeNat_injective {a b : Instr} : encodeNat a = encodeNat b → a = b := by
  cases a <;> cases b <;> injective_tac

theorem mem_umullForms {i : Instr} {lo hi n m : Fin 8} :
    i ∈ umullForms lo hi n m ↔ ∃ h, i = .umull lo hi n m h := by
  unfold umullForms
  split <;> simp_all

/-- The destinations of `UMULL` read back from its second halfword.  `mem_wideForms` rewrites with
these lemmas before `omega`, which reports a possible counterexample when it must refute the
equality of the two fields from the halfword's value alone. -/
theorem umull_lo (lo hi m : Fin 8) :
    (lo.val * 4096 + hi.val * 256 + m.val) / 4096 % 8 = lo.val := by
  omega

theorem umull_hi (lo hi m : Fin 8) :
    (lo.val * 4096 + hi.val * 256 + m.val) / 256 % 8 = hi.val := by
  omega

set_option maxHeartbeats 4000000 in
/-- The forms that `decode` tries on the halfwords of a 32-bit instruction include the
instruction.  For each form, the other candidates are different constructors, and the fields of
the form's own candidate read back as the instruction's with `omega`. -/
theorem mem_wideForms (i : Instr) (hw : wide (encodeNat i).1) :
    i ∈ wideForms (encodeNat i).1 (encodeNat i).2 := by
  cases i <;> simp only [wide, encodeNat] at hw <;>
    simp only [encodeNat, wideForms, field, List.cons_append, List.nil_append, List.mem_cons,
      mem_umullForms, reduceCtorEq, Instr.addReg.injEq, Instr.adcReg.injEq, Instr.subReg.injEq,
      Instr.sbcReg.injEq, Instr.andReg.injEq, Instr.orrReg.injEq, Instr.eorReg.injEq,
      Instr.cmpReg.injEq, Instr.lslReg.injEq, Instr.lsrReg.injEq, Instr.lslImm.injEq,
      Instr.lsrImm.injEq, Instr.subImm.injEq, Instr.andImm.injEq, Instr.eorImm.injEq,
      Instr.cmpImm.injEq, Instr.movImm.injEq, Instr.movw.injEq, Instr.movt.injEq,
      Instr.addwSp.injEq, Instr.subwSp.injEq, Instr.addwSpSp.injEq, Instr.subwSpSp.injEq,
      Instr.clz.injEq, Instr.umull.injEq, Instr.mla.injEq, Instr.mls.injEq, Instr.udiv.injEq,
      Instr.ldr.injEq, Instr.str.injEq, Instr.ldrSp.injEq, Instr.strSp.injEq, Instr.ldrLr.injEq,
      Instr.strLr.injEq, Instr.bcond.injEq, Instr.b.injEq, Instr.bl.injEq, Fin.ext_iff,
      umull_lo, umull_hi, exists_prop, ne_eq, false_or, or_false, true_and, and_true,
      and_false] at * <;>
    omega

/-- `find?` returns the element that satisfies the predicate when it is the only one. -/
theorem find?_unique {α : Type} {p : α → Bool} {a : α} :
    ∀ {l : List α}, a ∈ l → p a = true → (∀ b ∈ l, p b = true → b = a) → l.find? p = some a
  | [], h, _, _ => by cases h
  | b :: l, hm, hp, hu => by
      by_cases hb : p b = true
      · rw [List.find?_cons_of_pos hb, hu b List.mem_cons_self hb]
      · rw [List.find?_cons_of_neg hb]
        rcases List.mem_cons.mp hm with rfl | hm
        · exact absurd hp hb
        · exact find?_unique hm hp fun c hc => hu c (List.mem_cons_of_mem _ hc)

/-- The decoder reads every encoded instruction back as itself, whatever halfwords follow it. -/
theorem decode_encode (i : Instr) (rest : List UInt16) :
    decode (encode i ++ rest) = some (i, (encode i).length) := by
  obtain ⟨h1, h2⟩ := encodeNat_lt i
  by_cases hw : wide (encodeNat i).1
  · simp only [encode, hw, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil, decode, UInt16.toNat_ofNat_of_lt' h1, UInt16.toNat_ofNat_of_lt' h2]
    rw [find?_unique (p := fun c => encodeNat c == ((encodeNat i).1, (encodeNat i).2))
      (mem_wideForms i hw) (beq_iff_eq.mpr rfl)
      fun b _ hb => encodeNat_injective (beq_iff_eq.mp hb)]
    rfl
  · have hi : i = .bxLr := Classical.byContradiction fun h => hw ((wide_encodeNat i).mpr h)
    subst hi
    rfl

/-- Every instruction that the decoder reads from halfwords is the encoding of the instruction it
returns: the decoder accepts only the bit patterns that the encoder writes. -/
theorem decode_sound {hs : List UInt16} {i : Instr} {n : Nat} (h : decode hs = some (i, n)) :
    hs.take n = encode i := by
  cases hs with
  | nil => simp [decode] at h
  | cons h1 rest =>
    by_cases hw : wide h1.toNat
    · simp only [decode, hw, ↓reduceIte] at h
      cases rest with
      | nil => simp at h
      | cons h2 rest =>
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨c, hc, rfl, rfl⟩ := h
        have hp := List.find?_some hc
        have he : encodeNat c = (h1.toNat, h2.toNat) := beq_iff_eq.mp hp
        rw [show (h1 :: h2 :: rest).take 2 = [h1, h2] from rfl]
        simp only [encode, he, hw, ↓reduceIte, UInt16.ofNat_toNat]
    · simp only [decode, hw, ↓reduceIte] at h
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨c, hc, rfl, rfl⟩ := h
      have hp := List.find?_some hc
      have he : (encodeNat c).1 = h1.toNat := beq_iff_eq.mp hp
      rw [show (h1 :: rest).take 1 = [h1] from rfl]
      simp only [encode, he, hw, ↓reduceIte, UInt16.ofNat_toNat]

/-! The forms whose encodings split an immediate, built from the immediate as a number. -/

/-- `ADD{S}.W Rd, Rn, Rm, LSL #k`, for `k` from 0 to 31. -/
def Instr.addLsl (s : Fin 2) (d n m : Fin 8) (k : Nat) : Instr :=
  .addReg s d n m (field 8 (k / 4)) (field 4 k)

/-- `LSL.W Rd, Rm, #k`, for `k` from 0 to 31. -/
def Instr.lslBy (d m : Fin 8) (k : Nat) : Instr :=
  .lslImm d m (field 8 (k / 4)) (field 4 k)

/-- `LSR.W Rd, Rm, #k`, for `k` from 1 to 32, whose fields for 32 are those of 0. -/
def Instr.lsrBy (d m : Fin 8) (k : Nat) : Instr :=
  .lsrImm d m (field 8 (k / 4)) (field 4 k)

/-- `MOVW Rd, #v`, for `v` below 2^16. -/
def Instr.movwOf (d : Fin 8) (v : Nat) : Instr :=
  .movw d (field 16 (v / 4096)) (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v)

/-- `MOVT Rd, #v`, for `v` below 2^16. -/
def Instr.movtOf (d : Fin 8) (v : Nat) : Instr :=
  .movt d (field 16 (v / 4096)) (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v)

/-- `ADDW Rd, SP, #v`, for `v` below 4096. -/
def Instr.addwSpOf (d : Fin 8) (v : Nat) : Instr :=
  .addwSp d (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v)

/-- `SUBW Rd, SP, #v`, for `v` below 4096. -/
def Instr.subwSpOf (d : Fin 8) (v : Nat) : Instr :=
  .subwSp d (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v)

/-- `ADDW SP, SP, #v`, for `v` below 4096. -/
def Instr.addwSpSpOf (v : Nat) : Instr :=
  .addwSpSp (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v)

/-- `SUBW SP, SP, #v`, for `v` below 4096. -/
def Instr.subwSpSpOf (v : Nat) : Instr :=
  .subwSpSp (field 2 (v / 2048)) (field 8 (v / 256)) (field 256 v)

/-- `B<cond>.W` with the byte offset `off` from the instruction's address plus 4, for an even
`off` from -2^20 to 2^20 - 2. -/
def Instr.bcondTo (cond : Fin 14) (off : Int) : Instr :=
  let v := (off % 2097152).toNat
  .bcond cond (field 2 (v / 1048576)) (field 2 (v / 262144)) (field 2 (v / 524288))
    (field 64 (v / 4096)) (field 2048 (v / 2))

/-- The fields `S`, `J1`, `J2`, `imm10`, and `imm11` of `B.W` and `BL` for the byte offset `off`,
where `J1` is `NOT(I1) EOR S` and `J2` is `NOT(I2) EOR S`. -/
def branchFields (off : Int) : Fin 2 × Fin 2 × Fin 2 × Fin 1024 × Fin 2048 :=
  let v := (off % 33554432).toNat
  let s := v / 16777216 % 2
  (field 2 s, field 2 (1 - v / 8388608 % 2 + s), field 2 (1 - v / 4194304 % 2 + s),
    field 1024 (v / 4096), field 2048 (v / 2))

/-- `B.W` with the byte offset `off` from the instruction's address plus 4, for an even `off` from
-2^24 to 2^24 - 2. -/
def Instr.bTo (off : Int) : Instr :=
  let (s, j1, j2, imm10, imm11) := branchFields off
  .b s j1 j2 imm10 imm11

/-- `BL` with the byte offset `off` from the instruction's address plus 4, for an even `off` from
-2^24 to 2^24 - 2. -/
def Instr.blTo (off : Int) : Instr :=
  let (s, j1, j2, imm10, imm11) := branchFields off
  .bl s j1 j2 imm10 imm11

end LeanExe.M7
