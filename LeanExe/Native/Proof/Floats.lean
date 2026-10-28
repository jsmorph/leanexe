import LeanExe.Native.Proof.Ops
import LeanExe.Native.Proof.MemOps
import LeanExe.ProofKit.F64Bits

/-!
The simulation of the binary64 forms.

Talos's `IEEE64` operations that round return the positive canonical quiet NaN whenever their
result is a NaN, which LeanExe's `F64Bits` lemmas give through Lean's model of `Float`, whose
only NaN is that one (`canon_add` and the lemmas after it).  The Lean copy of Clight returns the
same bits when the result is a number and some quiet NaN of `Archi`'s choice otherwise
(`canonOf_binop`), so `canonStmt`, which replaces a NaN by the canonical NaN through `lx_pun`,
makes the C result Talos's for every `Archi`.  A comparison, `abs`, and the conversion from a
word agree with Talos's by the definitions of the copy.  A reinterpretation stores into
`lx_pun` at one type and loads at the other, and `trunc_sat` follows Talos's case analysis
through its three guards.

`push_exec` turns a C statement that sets the slot of the result, and changes no other
temporary but call results, into an `Outcome`.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## Talos's NaN results -/

/-- `r`, with a NaN replaced by the canonical NaN. -/
def canonOf (r : UInt64) : UInt64 := if IEEE64.isNaN r then IEEE64.canonicalNaN else r

theorem canonOf_float (x : _root_.Float) : canonOf x.toBits = x.toBits :=
  LeanExe.ProofKit.F64Bits.toBits_canonical x

theorem toBits_ofBits_num {w : UInt64} (h : IEEE64.isNaN w = false) :
    (_root_.Float.ofBits w).toBits = w := by
  rw [LeanExe.ProofKit.F64Bits.toBits_ofBits, h]
  rfl

theorem canonOf_canonical : canonOf IEEE64.canonicalNaN = IEEE64.canonicalNaN := by
  unfold canonOf
  split <;> rfl

theorem canon_add (a b : UInt64) : canonOf (IEEE64.add a b) = IEEE64.add a b := by
  cases ha : IEEE64.isNaN a
  · cases hb : IEEE64.isNaN b
    · rw [← toBits_ofBits_num ha, ← toBits_ofBits_num hb, ← LeanExe.ProofKit.F64Bits.toBits_add]
      exact canonOf_float _
    · have : IEEE64.add a b = IEEE64.canonicalNaN := by simp [IEEE64.add, hb]
      rw [this, canonOf_canonical]
  · have : IEEE64.add a b = IEEE64.canonicalNaN := by simp [IEEE64.add, ha]
    rw [this, canonOf_canonical]

theorem canon_sub (a b : UInt64) : canonOf (IEEE64.sub a b) = IEEE64.sub a b := by
  cases ha : IEEE64.isNaN a
  · cases hb : IEEE64.isNaN b
    · rw [← toBits_ofBits_num ha, ← toBits_ofBits_num hb, ← LeanExe.ProofKit.F64Bits.toBits_sub]
      exact canonOf_float _
    · have : IEEE64.sub a b = IEEE64.canonicalNaN := by
        simp [IEEE64.sub, IEEE64.add, LeanExe.ProofKit.F64Sign.isNaN_negate, hb]
      rw [this, canonOf_canonical]
  · have : IEEE64.sub a b = IEEE64.canonicalNaN := by simp [IEEE64.sub, IEEE64.add, ha]
    rw [this, canonOf_canonical]

theorem canon_mul (a b : UInt64) : canonOf (IEEE64.mul a b) = IEEE64.mul a b := by
  cases ha : IEEE64.isNaN a
  · cases hb : IEEE64.isNaN b
    · rw [← toBits_ofBits_num ha, ← toBits_ofBits_num hb, ← LeanExe.ProofKit.F64Bits.toBits_mul]
      exact canonOf_float _
    · have : IEEE64.mul a b = IEEE64.canonicalNaN := by simp [IEEE64.mul, hb]
      rw [this, canonOf_canonical]
  · have : IEEE64.mul a b = IEEE64.canonicalNaN := by simp [IEEE64.mul, ha]
    rw [this, canonOf_canonical]

theorem canon_div (a b : UInt64) : canonOf (IEEE64.div a b) = IEEE64.div a b := by
  cases ha : IEEE64.isNaN a
  · cases hb : IEEE64.isNaN b
    · rw [← toBits_ofBits_num ha, ← toBits_ofBits_num hb, ← LeanExe.ProofKit.F64Bits.toBits_div]
      exact canonOf_float _
    · have : IEEE64.div a b = IEEE64.canonicalNaN := by simp [IEEE64.div, hb]
      rw [this, canonOf_canonical]
  · have : IEEE64.div a b = IEEE64.canonicalNaN := by simp [IEEE64.div, ha]
    rw [this, canonOf_canonical]

theorem canon_sqrt (a : UInt64) : canonOf (IEEE64.sqrt a) = IEEE64.sqrt a := by
  cases ha : IEEE64.isNaN a
  · rw [← toBits_ofBits_num ha, ← LeanExe.ProofKit.F64Bits.toBits_sqrt]
    exact canonOf_float _
  · have : IEEE64.sqrt a = IEEE64.canonicalNaN := by simp [IEEE64.sqrt, ha]
    rw [this, canonOf_canonical]

/-! ## The copy's NaN results -/

theorem isNaN_quiet_nan_64 (sp : Bool × Nat) : IEEE64.isNaN (quiet_nan_64 sp) = true := by
  have hq : (quiet_nan_64_payload sp.2).testBit 51 = true := by
    unfold quiet_nan_64_payload
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow_self]
    simp
  have hlt : quiet_nan_64_payload sp.2 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hne : quiet_nan_64_payload sp.2 ≠ 0 := fun h => by simp [h] at hq
  have hv : (quiet_nan_64 sp).toNat =
      (if sp.1 then 2 ^ 63 else 0) + 0x7FF * 2 ^ 52 + quiet_nan_64_payload sp.2 := by
    unfold quiet_nan_64
    rw [UInt64.toNat_ofNat']
    split <;> omega
  simp only [IEEE64.isNaN, IEEE64.exponent, IEEE64.fraction, hv, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq]
  split <;> omega

/-- The copy's result of an operation whose Talos result is `r`, canonicalized, is `r`
canonicalized. -/
theorem canonOf_binop (A : Archi) (r x y : UInt64) :
    canonOf (LClight.Float.binop A r x y) = canonOf r := by
  unfold LClight.Float.binop canonOf
  cases h : IEEE64.isNaN r
  · simp [h]
  · simp [LClight.Float.binop_nan, isNaN_quiet_nan_64]

theorem canonOf_sqrt (A : Archi) (x : UInt64) : canonOf (LClight.Float.sqrt A x) = IEEE64.sqrt x := by
  rw [← canon_sqrt x]
  unfold LClight.Float.sqrt canonOf
  cases h : IEEE64.isNaN (IEEE64.sqrt x)
  · simp [h]
  · simp [LClight.Float.unop_nan, isNaN_quiet_nan_64, h]

/-! ## Comparisons -/

theorem cmp_ne_self (x : UInt64) : LClight.Float.cmp .Cne x x = IEEE64.isNaN x := by
  unfold LClight.Float.cmp LClight.Float.compare
  cases h : IEEE64.isNaN x
  · simp [IEEE64.eq, h, cmp_of_comparison]
  · simp [cmp_of_comparison]

theorem cmp_eq (x y : UInt64) : LClight.Float.cmp .Ceq x y = IEEE64.eq x y := by
  unfold LClight.Float.cmp LClight.Float.compare
  split
  · rename_i h
    simp [IEEE64.eq, h, cmp_of_comparison]
  · split
    · rename_i _ he; simp [he, cmp_of_comparison]
    · rename_i _ he
      split <;> simp [cmp_of_comparison, he]

theorem cmp_lt (x y : UInt64) : LClight.Float.cmp .Clt x y = IEEE64.lt x y := by
  unfold LClight.Float.cmp LClight.Float.compare
  split
  · rename_i h
    simp [IEEE64.lt, h, cmp_of_comparison]
  · rename_i hn
    split
    · rename_i he
      simp only [IEEE64.eq, IEEE64.lt, Bool.or_eq_true, not_or] at hn he ⊢
      simp only [hn.1, hn.2, Bool.false_eq_true, or_self, ite_false, beq_iff_eq] at he ⊢
      simp [cmp_of_comparison, he]
    · rename_i hne
      split
      · rename_i hl; simp [cmp_of_comparison, hl]
      · rename_i hl; simp [cmp_of_comparison, Bool.eq_false_iff.mpr hl]

theorem cmp_le (x y : UInt64) : LClight.Float.cmp .Cle x y = IEEE64.le x y := by
  unfold LClight.Float.cmp LClight.Float.compare
  split
  · rename_i h
    simp [IEEE64.le, h, cmp_of_comparison]
  · rename_i hn
    simp only [Bool.or_eq_true, not_or] at hn
    have hn1 : IEEE64.isNaN x = false := Bool.eq_false_iff.mpr hn.1
    have hn2 : IEEE64.isNaN y = false := Bool.eq_false_iff.mpr hn.2
    split
    · rename_i he
      simp only [IEEE64.eq, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
        beq_iff_eq] at he
      simp [cmp_of_comparison, IEEE64.le, hn1, hn2, he]
    · rename_i hne
      simp only [IEEE64.eq, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
        beq_iff_eq] at hne
      split
      · rename_i hl
        simp only [IEEE64.lt, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
          decide_eq_true_eq] at hl
        simp [cmp_of_comparison, IEEE64.le, hn1, hn2]
        omega
      · rename_i hl
        simp only [IEEE64.lt, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
          decide_eq_true_eq] at hl
        simp [cmp_of_comparison, IEEE64.le, hn1, hn2]
        omega

/-- `Cge` is the reverse of `Cle`. -/
theorem cmp_ge (x y : UInt64) : LClight.Float.cmp .Cge x y = IEEE64.le y x := by
  rw [← cmp_le]
  unfold LClight.Float.cmp LClight.Float.compare
  by_cases hn : IEEE64.isNaN x = true ∨ IEEE64.isNaN y = true
  · rcases hn with hn | hn <;> simp [hn, cmp_of_comparison]
  · simp only [not_or] at hn
    have hn1 : IEEE64.isNaN x = false := Bool.eq_false_iff.mpr hn.1
    have hn2 : IEEE64.isNaN y = false := Bool.eq_false_iff.mpr hn.2
    simp only [hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false, IEEE64.eq, IEEE64.lt,
      beq_iff_eq, decide_eq_true_eq]
    by_cases h1 : IEEE64.scaledValue x = IEEE64.scaledValue y
    · simp [h1, cmp_of_comparison]
    · by_cases h2 : IEEE64.scaledValue x < IEEE64.scaledValue y
      · have h3 : ¬ IEEE64.scaledValue y = IEEE64.scaledValue x := fun e => h1 e.symm
        have h4 : ¬ IEEE64.scaledValue y < IEEE64.scaledValue x := by omega
        simp [h1, h2, h3, h4, cmp_of_comparison]
      · have h3 : ¬ IEEE64.scaledValue y = IEEE64.scaledValue x := fun e => h1 e.symm
        have h4 : IEEE64.scaledValue y < IEEE64.scaledValue x := by omega
        simp [h1, h2, h3, h4, cmp_of_comparison]

/-! ## `trunc_sat` -/

/-- -1.0. -/
def m1Bits : UInt64 := 0xBFF0000000000000
/-- 2^64. -/
def t64Bits : UInt64 := 0x43F0000000000000

theorem sv_m1 : IEEE64.scaledValue m1Bits = -(2 ^ 1074 : Int) := by decide +kernel
theorem sv_t64 : IEEE64.scaledValue t64Bits = (2 ^ 1138 : Int) := by decide +kernel

set_option exponentiation.threshold 2100 in
theorem mag_inf (x : UInt64) (hf : IEEE64.isFinite x = false) :
    2 ^ 1138 ≤ IEEE64.scaledMagnitude x := by
  simp only [IEEE64.isFinite, bne_eq_false_iff_eq] at hf
  unfold IEEE64.scaledMagnitude
  rw [hf]
  simp only [beq_iff_eq, show (2047 : Nat) ≠ 0 from by decide, ite_false]
  calc 2 ^ 1138 ≤ 2 ^ (2047 - 1) := Nat.pow_le_pow_right (by decide) (by decide)
    _ ≤ (2 ^ 52 + IEEE64.fraction x) * 2 ^ (2047 - 1) :=
      Nat.le_mul_of_pos_left _ (by have := Nat.one_le_two_pow (n := 52); omega)

set_option exponentiation.threshold 2100 in
/-- Talos's `i64.trunc_sat_f64_u` of a number, through the guards of `truncSatStmt`: 0 at or below
-1, the largest word at or above 2^64, and the C conversion between. -/
theorem truncSat_cases (x : UInt64) (hn : IEEE64.isNaN x = false) :
    (IEEE64.le x m1Bits = true → IEEE64.truncSatI64U x = 0) ∧
    (IEEE64.le x m1Bits = false → IEEE64.le t64Bits x = true →
      IEEE64.truncSatI64U x = 0xFFFFFFFFFFFFFFFF) ∧
    (IEEE64.le x m1Bits = false → IEEE64.le t64Bits x = false →
      LClight.Float.to_longu x = some (IEEE64.truncSatI64U x)) := by
  have hm1n : IEEE64.isNaN m1Bits = false := by decide
  have htn : IEEE64.isNaN t64Bits = false := by decide
  have hle1 : IEEE64.le x m1Bits = decide (IEEE64.scaledValue x ≤ -(2 ^ 1074 : Int)) := by
    simp [IEEE64.le, hn, hm1n, sv_m1]
  have hle2 : IEEE64.le t64Bits x = decide ((2 ^ 1138 : Int) ≤ IEEE64.scaledValue x) := by
    simp [IEEE64.le, hn, htn, sv_t64]
  rw [hle1, hle2]
  have hinf := mag_inf x
  unfold IEEE64.truncSatI64U LClight.Float.to_longu LClight.Float.ZofB_range IEEE64.truncatedInt
  unfold IEEE64.scaledValue
  simp only [hn, Bool.false_eq_true, ite_false]
  generalize IEEE64.scaledMagnitude x = M at *
  have hP : (0 : Int) < 2 ^ 1074 := by positivity
  have h0 : (0 : Int) ≤ (M : Int) / 2 ^ 1074 := Int.ediv_nonneg (by omega) hP.le
  have hlt : M < 2 ^ 1138 → (M : Int) / 2 ^ 1074 < 2 ^ 64 := fun h =>
    Int.ediv_lt_of_lt_mul hP (by
      have : ((2 : Int) ^ 64 * 2 ^ 1074) = 2 ^ 1138 := by rw [← pow_add]
      push_cast [this] at h ⊢; omega)
  have hge : 2 ^ 1138 ≤ M → (2 : Int) ^ 64 ≤ (M : Int) / 2 ^ 1074 := fun h =>
    Int.le_ediv_of_mul_le hP (by
      have : ((2 : Int) ^ 64 * 2 ^ 1074) = 2 ^ 1138 := by rw [← pow_add]
      rw [this]; exact_mod_cast h)
  have hz : M < 2 ^ 1074 → (M : Int) / 2 ^ 1074 = 0 := fun h =>
    Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast h)
  have hpos : 2 ^ 1074 ≤ M → (1 : Int) ≤ (M : Int) / 2 ^ 1074 := fun h =>
    Int.le_ediv_of_mul_le hP (by rw [one_mul]; exact_mod_cast h)
  have hnat : ((M / 2 ^ 1074 : Nat) : Int) = (M : Int) / 2 ^ 1074 := by push_cast; rfl
  have hmax : Int64.max_unsigned = 2 ^ 64 - 1 := rfl
  cases hs : IEEE64.sign x <;> cases hfin : IEEE64.isFinite x <;>
    simp only [hfin, hnat, Bool.false_eq_true, ite_false, ite_true] at hinf ⊢
  all_goals
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le, true_implies] at *
    generalize hq : (M : Int) / 2 ^ 1074 = q at *
  -- positive, infinite
  · exact ⟨fun h => by omega, fun _ _ => trivial, fun _ h => by omega⟩
  -- positive, finite
  · refine ⟨fun h => by omega, fun _ h => ?_, fun _ h => ?_⟩
    · have := hge (by exact_mod_cast h)
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · have hq1 := hlt (by exact_mod_cast h)
      rw [ite_eq_left (show 0 ≤ q ∧ q ≤ Int64.max_unsigned from ⟨h0, by rw [hmax]; omega⟩),
        Option.map_some]
      congr 1
      split
      · obtain rfl : q = 0 := by omega
        rfl
      · split
        · obtain rfl : q = 2 ^ 64 - 1 := by omega
          decide +kernel
        · unfold Int64.repr IEEE64.intToUInt64
          rw [ite_eq_right (by omega), Int64.modulus, Int.emod_eq_of_lt (by omega) (by omega)]
          congr 1
          omega
  -- negative, infinite
  · exact ⟨fun _ => trivial, fun _ h => by omega, fun h _ => by omega⟩
  -- negative, finite
  · refine ⟨fun h => ?_, fun _ h => by omega, fun h _ => ?_⟩
    · have := hpos (by exact_mod_cast (by omega : (2 : Int) ^ 1074 ≤ M))
      rw [ite_eq_left (by omega)]
    · have hq0 := hz (by exact_mod_cast (by omega : (M : Int) < 2 ^ 1074))
      subst hq0
      rw [ite_eq_left (show 0 ≤ -(0 : Int) ∧ -(0 : Int) ≤ Int64.max_unsigned from
        ⟨by omega, by rw [hmax]; omega⟩), Option.map_some, ite_eq_left (by omega)]
      rfl

/-! ## Negation of a constant -/

theorem negate_negate (v : UInt64) : IEEE64.negate (IEEE64.negate v) = v := by
  obtain ⟨he, hf, hs⟩ := LeanExe.ProofKit.F64Sign.fields_negate v
  show IEEE64.encodeFinite (!IEEE64.sign (IEEE64.negate v)) (IEEE64.exponent (IEEE64.negate v))
    (IEEE64.fraction (IEEE64.negate v)) = v
  rw [he, hf, hs, Bool.not_not, LeanExe.ProofKit.F64Packing.encode_fields]

/-! ## Values on the stack -/

theorem has_f64 {v : Value} (h : VT.has .f64 v = true) : ∃ x, v = .f64 x := by
  cases v <;> simp_all [VT.has]

theorem pop1_f64 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.f64 :: σr) vs) :
    ∃ x vr, vs = .f64 x :: vr ∧ le[slotId σr.length .f64]? = some (.Vfloat x) ∧
      StackRel le σr vr := by
  obtain ⟨v1, vr, rfl, h1, hl1, hrest⟩ := h.cons_inv
  obtain ⟨x, rfl⟩ := has_f64 h1
  exact ⟨x, vr, rfl, hl1, hrest⟩

theorem pop2_f64 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.f64 :: .f64 :: σr) vs) :
    ∃ y x vr, vs = .f64 y :: .f64 x :: vr ∧ le[slotId (σr.length + 1) .f64]? = some (.Vfloat y) ∧
      le[slotId σr.length .f64]? = some (.Vfloat x) ∧ StackRel le σr vr := by
  obtain ⟨v1, vs1, rfl, h1, hl1, h'⟩ := h.cons_inv
  obtain ⟨v2, vr, rfl, h2, hl2, hrest⟩ := h'.cons_inv
  obtain ⟨y, rfl⟩ := has_f64 h1
  obtain ⟨x, rfl⟩ := has_f64 h2
  exact ⟨y, x, vr, rfl, hl1, hl2, hrest⟩

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-! ## The result of a statement -/

/-- A statement that sets the slot at height `σr.length` to `v` of type `t` and changes no other
temporary but the results of calls, in a memory related to the store with `lx_status` 0. -/
theorem push_exec {L : List Label} {σr : List VT} {α : Type} {st : Store α} {sl : Locals}
    {le le' : temp_env} {m m' : mem} {s : statement} {v : Value} {t : VT} {vr : List Value}
    (hrest : StackRel le σr vr) (hloc : LocalsRel le c.locals (sl.params ++ sl.locals))
    (hb : le[brkId]? = some (.Vint 0)) (hbase : curBase L ≤ σr.length)
    (hx : exec_stmt A X E.ge empty_env le m s E0 le' m' .Out_normal)
    (hslot : le'[slotId σr.length t]? = some (cval v)) (ht : t.has v = true)
    (hkeep : ∀ id, id ≠ slotId σr.length t → (∀ k, id ≠ callId k) → le'[id]? = le[id]?)
    (hg : StoreRel E st m') (hs : StatusRel E m' 0) :
    Outcome A X E c L (some (t :: σr))
      (.Fallthrough st { params := sl.params, locals := sl.locals, values := v :: vr }) s le m := by
  have hfr : Frame σr.length le le' := fun h' hh t' =>
    hkeep _ (slotId_ne_of_height _ _ (by omega)) (fun k => (callId_ne_slotId k h' t').symm)
  refine ⟨t :: σr, rfl, by simp; omega, E0, le', m', hx, ?_, hfr.mono hbase⟩
  exact { stack := ⟨ht, hslot, hrest.frame hfr⟩
          locals := ⟨hloc.1, fun i hi => by
            obtain ⟨w, hw, htw, hl⟩ := hloc.2 i hi
            exact ⟨w, hw, htw, by
              rw [hkeep _ (slotId_ne_localId _ _ i).symm (fun k => (callId_ne_localId k i).symm)]
              exact hl⟩⟩
          store := hg
          status := hs
          brk := by
            rw [hkeep _ (slotId_ne_brkId _ _).symm (fun k => (callId_ne_brkId k).symm)]
            exact hb }

/-! ## `lx_pun` -/

theorem eval_punVar (hE : EnvOk E) (le : temp_env) (m : mem) :
    eval_expr A E.ge empty_env le m (.Evar punId punType) (.Vptr E.pun Ptrofs.zero) :=
  .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hE.pun) (.deref_loc_reference rfl)

theorem eval_punAt_lvalue (hE : EnvOk E) (le : temp_env) (m : mem) (ty : type) :
    eval_lvalue A E.ge empty_env le m (punAt ty) E.pun Ptrofs.zero .Full :=
  .eval_Ederef _ _ _ _ (.eval_Ecast _ _ _ _ (eval_punVar hE le m) rfl)

theorem eval_punAt_double (hE : EnvOk E) {le : temp_env} {m : mem} {x : UInt64}
    (hl : Mem.load .Mfloat64 m E.pun 0 = some (.Vfloat x)) :
    eval_expr A E.ge empty_env le m (punAt tdouble) (.Vfloat x) :=
  .eval_Elvalue _ _ _ _ _ (eval_punAt_lvalue hE le m _)
    (.deref_loc_value .Mfloat64 _ rfl (by rw [loadv_zero _ _ _ (by decide)]; exact hl))

theorem eval_punAt_long (hE : EnvOk E) {le : temp_env} {m : mem} {x : UInt64}
    (hl : Mem.load .Mint64 m E.pun 0 = some (.Vlong x)) :
    eval_expr A E.ge empty_env le m (punAt tulong) (.Vlong x) :=
  .eval_Elvalue _ _ _ _ _ (eval_punAt_lvalue hE le m _)
    (.deref_loc_value .Mint64 _ rfl (by rw [loadv_zero _ _ _ (by decide)]; exact hl))

theorem exec_punAssign_long (hE : EnvOk E) {le : temp_env} {m : mem} {e : expr} {x : UInt64}
    (he : eval_expr A E.ge empty_env le m e (.Vlong x)) (hty : typeof e = tulong)
    (hva : Mem.valid_access m .Mint64 E.pun 0 .Writable) :
    exec_stmt A X E.ge empty_env le m (.Sassign (punAt tulong) e) E0 le
      (Mem.stored .Mint64 m E.pun 0 (.Vlong x)) .Out_normal :=
  .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ (eval_punAt_lvalue hE le m _) he (by rw [hty]; rfl)
    (.assign_loc_value _ .Mint64 _ rfl
      (by rw [storev_zero _ _ _ _ (by decide)]; exact Mem.store_ok _ hva))

theorem exec_punAssign_double (hE : EnvOk E) {le : temp_env} {m : mem} {e : expr} {x : UInt64}
    (he : eval_expr A E.ge empty_env le m e (.Vfloat x)) (hty : typeof e = tdouble)
    (hva : Mem.valid_access m .Mfloat64 E.pun 0 .Writable) :
    exec_stmt A X E.ge empty_env le m (.Sassign (punAt tdouble) e) E0 le
      (Mem.stored .Mfloat64 m E.pun 0 (.Vfloat x)) .Out_normal :=
  .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ (eval_punAt_lvalue hE le m _) he (by rw [hty]; rfl)
    (.assign_loc_value _ .Mfloat64 _ rfl
      (by rw [storev_zero _ _ _ _ (by decide)]; exact Mem.store_ok _ hva))

theorem StoreRel.store_pun {α : Type} {st : Store α} {m : mem} (hE : EnvOk E)
    (h : StoreRel E st m) (chunk : memory_chunk) (v : val) :
    StoreRel E st (Mem.stored chunk m E.pun 0 v) :=
  ⟨GlobalsRel.sameExcept h.1 (Mem.SameExcept.of_stored _ _ _ _ _) hE.pun_other.2.2.2,
    h.2.store_other _ hE.pun_other.2.1 hE.pun_other.2.2.1 _ _⟩

theorem StatusRel.store_pun {m : mem} {k : Nat} (hE : EnvOk E) (h : StatusRel E m k)
    (chunk : memory_chunk) (v : val) : StatusRel E (Mem.stored chunk m E.pun 0 v) k :=
  h.sameExcept (Mem.SameExcept.of_stored _ _ _ _ _) (Ne.symm hE.pun_other.1)

/-- `punStore w h`: the slot of the double at height `h` gets the bits of the word `w`. -/
theorem exec_punStore (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} {m : mem}
    {e : expr} {x : UInt64} {h : Nat} (he : eval_expr A E.ge empty_env le m e (.Vlong x))
    (hty : typeof e = tulong) (hst : StoreRel E st m) :
    exec_stmt A X E.ge empty_env le m (punStore e h) E0 (le.insert (slotId h .f64) (.Vfloat x))
      (Mem.stored .Mint64 m E.pun 0 (.Vlong x)) .Out_normal :=
  .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (exec_punAssign_long hE he hty hst.2.punW)
    (.exec_Sset _ _ _ _ _ _ (eval_punAt_double hE (Mem.load_float_stored_long _ _ _ _ hst.2.punW)))

/-- `canonStmt h` replaces a NaN in the double slot at height `h` by the canonical NaN. -/
theorem exec_canon (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} {m : mem} {h : Nat}
    {q : UInt64} (hq : le[slotId h .f64]? = some (.Vfloat q)) (hst : StoreRel E st m)
    (hs : StatusRel E m 0) :
    ∃ le' m', exec_stmt A X E.ge empty_env le m (canonStmt h) E0 le' m' .Out_normal ∧
      le'[slotId h .f64]? = some (.Vfloat (canonOf q)) ∧
      (∀ id, id ≠ slotId h .f64 → le'[id]? = le[id]?) ∧ StoreRel E st m' ∧ StatusRel E m' 0 := by
  have hc : eval_expr A E.ge empty_env le m (.Ebinop .One (tmp h .f64) (tmp h .f64) tint)
      (Val.of_bool (IEEE64.isNaN q)) := by
    refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hq) (.eval_Etempvar _ _ _ hq) ?_
    show some (Val.of_bool (LClight.Float.cmp .Cne q q)) = _
    rw [cmp_ne_self]
  cases hn : IEEE64.isNaN q
  · refine ⟨le, m, ?_, ?_, fun _ _ => rfl, hst, hs⟩
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc ?_ (.exec_Sskip _ _ _)
      rw [hn]; rfl
    · rw [hq]; simp [canonOf, hn]
  · refine ⟨le.insert (slotId h .f64) (.Vfloat IEEE64.canonicalNaN),
      Mem.stored .Mint64 m E.pun 0 (.Vlong IEEE64.canonicalNaN), ?_, ?_,
      fun id hid => te_insert_ne _ (Ne.symm hid), hst.store_pun hE _ _, hs.store_pun hE _ _⟩
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc ?_
        (exec_punStore hE (.eval_Econst_long _ _) rfl hst)
      rw [hn]; rfl
    · rw [te_insert_same]; simp [canonOf, hn]

end

/-! ## The forms -/

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

theorem of_bool_eq (b : Bool) : Val.of_bool b = .Vint (if b then 1 else 0) := by
  cases b <;> rfl

/-- A binary64 operation that rounds. -/
theorem sim_ff (hE : EnvOk E) (F : Nat) (inst : Instruction) (op : binary_operation)
    (f : UInt64 → UInt64 → UInt64)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .f64 :: .f64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.f64 :: σr) ∧
        s = .Ssequence (.Sset (slotId σr.length .f64)
          (.Ebinop op (tmp σr.length .f64) (tmp (σr.length + 1) .f64) tdouble))
          (canonStmt σr.length))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .f64 y :: .f64 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        .Fallthrough st { params := sl.params, locals := sl.locals, values := .f64 (f x y) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, ∃ q, sem_binary_operation A op (.Vfloat x) tdouble (.Vfloat y) tdouble m =
      some (.Vfloat q) ∧ canonOf q = f x y) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_f64 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      obtain ⟨q, hq, hqf⟩ := hsem m x y
      have h1 : exec_stmt A X E.ge empty_env le m (.Sset (slotId σr.length .f64)
          (.Ebinop op (tmp σr.length .f64) (tmp (σr.length + 1) .f64) tdouble)) E0
          (le.insert (slotId σr.length .f64) (.Vfloat q)) m .Out_normal :=
        .exec_Sset _ _ _ _ _ _
          (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx) (.eval_Etempvar _ _ _ hy) hq)
      obtain ⟨le2, m2, h2, hslot, hk, hst2, hs2⟩ := exec_canon (A := A) (X := X) hE
        (te_insert_same le _ _) hinv.store hinv.status
      exact push_exec hrest hinv.locals hinv.brk hb (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2)
        (by rw [hslot, hqf]; rfl) rfl
        (fun id hid _ => by rw [hk id hid, te_insert_ne _ (Ne.symm hid)]) hst2 hs2

theorem tr_ff {inst : Instruction} {op : binary_operation} (hop : f64Op inst = some op)
    {L : List Label} {σ : List VT} {n : Nat} {s : statement} {σ' : Option (List VT)} {n' : Nat}
    (h : trInstr c L σ n inst = some (s, σ', n')) :
    ∃ σr, σ = .f64 :: .f64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧ σ' = some (.f64 :: σr) ∧
      s = .Ssequence (.Sset (slotId σr.length .f64)
        (.Ebinop op (tmp σr.length .f64) (tmp (σr.length + 1) .f64) tdouble))
        (canonStmt σr.length) := by
  have hinst : inst = .f64Add ∨ inst = .f64Sub ∨ inst = .f64Mul ∨ inst = .f64Div := by
    cases inst <;> simp [f64Op] at hop ⊢
  rcases hinst with rfl | rfl | rfl | rfl <;>
  · simp only [f64Op, Option.some.injEq] at hop
    subst hop
    rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
      simp [trInstr, f64Op, pops, Option.bind_eq_some_iff] at h
    obtain ⟨hb, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
    exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩

theorem sim_f64Add (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f64Add :=
  sim_ff hE F .f64Add .Oadd f64Add (fun _ _ _ _ _ _ h => tr_ff rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf (LClight.Float.binop A (IEEE64.add x y) x y) = _
      rw [canonOf_binop, canon_add]; rfl⟩)

theorem sim_f64Sub (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f64Sub :=
  sim_ff hE F .f64Sub .Osub f64Sub (fun _ _ _ _ _ _ h => tr_ff rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf (LClight.Float.binop A (IEEE64.sub x y) x y) = _
      rw [canonOf_binop, canon_sub]; rfl⟩)

theorem sim_f64Mul (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f64Mul :=
  sim_ff hE F .f64Mul .Omul f64Mul (fun _ _ _ _ _ _ h => tr_ff rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf (LClight.Float.binop A (IEEE64.mul x y) x y) = _
      rw [canonOf_binop, canon_mul]; rfl⟩)

theorem sim_f64Div (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f64Div :=
  sim_ff hE F .f64Div .Odiv f64Div (fun _ _ _ _ _ _ h => tr_ff rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf (LClight.Float.binop A (IEEE64.div x y) x y) = _
      rw [canonOf_binop, canon_div]; rfl⟩)

/-- A binary64 comparison. -/
theorem sim_fcmp (F : Nat) (inst : Instruction) (op : binary_operation) (f : UInt64 → UInt64 → Bool)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .f64 :: .f64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.i32 :: σr) ∧
        s = .Sset (slotId σr.length .i32)
          (.Ecast (.Ebinop op (tmp σr.length .f64) (tmp (σr.length + 1) .f64) tint) tuint))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .f64 y :: .f64 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        .Fallthrough st
          { params := sl.params, locals := sl.locals, values := .i32 (if f x y then 1 else 0) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, sem_binary_operation A op (.Vfloat x) tdouble (.Vfloat y) tdouble m =
      some (Val.of_bool (f x y))) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_f64 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      refine push_step hrest hinv.locals hinv.store hinv.status hinv.brk ?_ rfl hb
      refine .eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx)
        (.eval_Etempvar _ _ _ hy) (hsem m x y)) ?_
      rw [of_bool_eq]
      exact cast_int_uint m _

theorem tr_fcmp {inst : Instruction} {op : binary_operation} (hop : f64Cmp inst = some op)
    {L : List Label} {σ : List VT} {n : Nat} {s : statement} {σ' : Option (List VT)} {n' : Nat}
    (h : trInstr c L σ n inst = some (s, σ', n')) :
    ∃ σr, σ = .f64 :: .f64 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧ σ' = some (.i32 :: σr) ∧
      s = .Sset (slotId σr.length .i32)
        (.Ecast (.Ebinop op (tmp σr.length .f64) (tmp (σr.length + 1) .f64) tint) tuint) := by
  have hinst : inst = .f64Eq ∨ inst = .f64Lt ∨ inst = .f64Le := by
    cases inst <;> simp [f64Cmp] at hop ⊢
  rcases hinst with rfl | rfl | rfl <;>
  · simp only [f64Cmp, Option.some.injEq] at hop
    subst hop
    rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
      simp [trInstr, f64Cmp, pops, Option.bind_eq_some_iff] at h
    obtain ⟨hb, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
    exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩

theorem sim_f64Eq (F : Nat) : InstrSim A X E mod c F .f64Eq :=
  sim_fcmp F .f64Eq .Oeq f64Eq (fun _ _ _ _ _ _ h => tr_fcmp rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => by
      show some (Val.of_bool (LClight.Float.cmp .Ceq x y)) = _
      rw [cmp_eq]; rfl)

theorem sim_f64Lt (F : Nat) : InstrSim A X E mod c F .f64Lt :=
  sim_fcmp F .f64Lt .Olt f64Lt (fun _ _ _ _ _ _ h => tr_fcmp rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => by
      show some (Val.of_bool (LClight.Float.cmp .Clt x y)) = _
      rw [cmp_lt]; rfl)

theorem sim_f64Le (F : Nat) : InstrSim A X E mod c F .f64Le :=
  sim_fcmp F .f64Le .Ole f64Le (fun _ _ _ _ _ _ h => tr_fcmp rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => by
      show some (Val.of_bool (LClight.Float.cmp .Cle x y)) = _
      rw [cmp_le]; rfl)

theorem sim_f64Abs (F : Nat) : InstrSim A X E mod c F .f64Abs := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Eunop _ _ _ _ _ (.eval_Etempvar _ _ _ hx) rfl) rfl hb

theorem sim_f64ConvertI64U (F : Nat) : InstrSim A X E mod c F .f64ConvertI64U := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hx) rfl) rfl hb

theorem sim_f64ReinterpretI64 (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f64ReinterpretI64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_exec hrest hinv.locals hinv.brk hb
        (exec_punStore hE (.eval_Etempvar _ _ _ hx) rfl hinv.store) (te_insert_same _ _ _) rfl
        (fun id hid _ => te_insert_ne _ (Ne.symm hid)) (hinv.store.store_pun hE _ _)
        (hinv.status.store_pun hE _ _)

theorem sim_i64ReinterpretF64 (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .i64ReinterpretF64 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f64 hinv.stack
      simp only [execOne.eq_def, hvs]
      have hva : Mem.valid_access m .Mfloat64 E.pun 0 .Writable := hinv.store.2.punW
      exact push_exec hrest hinv.locals hinv.brk hb
        (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
          (exec_punAssign_double hE (.eval_Etempvar _ _ _ hx) rfl hva)
          (.exec_Sset _ _ _ _ _ _
            (eval_punAt_long hE (Mem.load_long_stored_float _ _ _ _ hinv.store.2.punW))))
        (te_insert_same _ _ _) rfl
        (fun id hid _ => te_insert_ne _ (Ne.symm hid)) (hinv.store.store_pun hE _ _)
        (hinv.status.store_pun hE _ _)

theorem sim_f64Const (hE : EnvOk E) (F : Nat) (v : UInt64) : InstrSim A X E mod c F (.f64Const v) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      simp only [execOne.eq_def]
      unfold f64ConstStmt
      split
      · split
        · rename_i hs
          refine push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk ?_ rfl hbase
          refine .eval_Eunop _ _ _ _ _ (.eval_Econst_float _ _) ?_
          show some (val.Vfloat (IEEE64.negate (IEEE64.negate v))) = _
          rw [negate_negate]; rfl
        · exact push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk
            (.eval_Econst_float _ _) rfl hbase
      · exact push_exec hinv.stack hinv.locals hinv.brk hbase
          (exec_punStore hE (.eval_Econst_long _ _) rfl hinv.store) (te_insert_same _ _ _) rfl
          (fun id hid _ => te_insert_ne _ (Ne.symm hid)) (hinv.store.store_pun hE _ _)
          (hinv.status.store_pun hE _ _)

end

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- The call of `__builtin_fsqrt` on an expression of type `double`. -/
theorem exec_sqrt_call (hE : EnvOk E) {le : temp_env} {m : mem} {k : Nat} {a : expr}
    {x : UInt64} (ha : eval_expr A E.ge empty_env le m a (.Vfloat x)) (hty : typeof a = tdouble) :
    exec_stmt A X E.ge empty_env le m (.Scall (some (callId k)) sqrtVar [a]) E0
      (le.insert (callId k) (.Vfloat (LClight.Float.sqrt A x))) m .Out_normal := by
  have hcallee : eval_expr A E.ge empty_env le m sqrtVar (.Vptr E.sqrt Ptrofs.zero) :=
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hE.sqrt) (.deref_loc_reference rfl)
  have hfind : Genv.find_funct E.ge (.Vptr E.sqrt Ptrofs.zero) = some sqrtFun := by
    simp [Genv.find_funct, hE.sqrt_fun]
  have hevl : eval_exprlist A E.ge empty_env le m [a] [tdouble] [.Vfloat x] :=
    .eval_Econs _ _ _ _ _ _ _ ha (by rw [hty]; rfl) .eval_Enil
  have hlook : lookup_builtin_function "__builtin_fsqrt" sqrtSig = some .BI_fsqrt := by decide
  have hcall : eval_funcall A X E.ge m sqrtFun [.Vfloat x] E0 m
      (.Vfloat (LClight.Float.sqrt A x)) := by
    refine .eval_funcall_external _ _ _ _ _ _ _ _ _ ?_
    show (match lookup_builtin_function "__builtin_fsqrt" sqrtSig with
      | some bf => known_builtin_sem A bf [.Vfloat x] m E0 (.Vfloat (LClight.Float.sqrt A x)) m
      | none => False)
    rw [hlook]
    exact ⟨rfl, rfl, rfl⟩
  exact .exec_Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl hcallee hevl hfind rfl hcall

theorem sim_f64Sqrt (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f64Sqrt := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f64 hinv.stack
      simp only [execOne.eq_def, hvs]
      have h1 := exec_sqrt_call (A := A) (X := X) (m := m) (k := n) hE
        (.eval_Etempvar _ _ _ hx) rfl
      let le1 := le.insert (callId n) (.Vfloat (LClight.Float.sqrt A x))
      have h2 : exec_stmt A X E.ge empty_env le1 m
          (.Sset (slotId σr.length .f64) (.Etempvar (callId n) tdouble)) E0
          (le1.insert (slotId σr.length .f64) (.Vfloat (LClight.Float.sqrt A x))) m .Out_normal :=
        .exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _))
      obtain ⟨le3, m3, h3, hslot, hk, hst3, hs3⟩ := exec_canon (A := A) (X := X) hE
        (te_insert_same le1 _ _) hinv.store hinv.status
      exact push_exec hrest hinv.locals hinv.brk hb
        (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2) h3)
        (by rw [hslot, canonOf_sqrt]; rfl) rfl
        (fun id hid hc => by
          rw [hk id hid, te_insert_ne _ (Ne.symm hid), te_insert_ne _ (Ne.symm (hc n))])
        hst3 hs3

theorem eval_minusOne {le : temp_env} {m : mem} :
    eval_expr A E.ge empty_env le m minusOne (.Vfloat m1Bits) :=
  .eval_Eunop _ _ _ _ _ (.eval_Econst_float _ _) rfl

/-- `truncSatStmt h` sets the word slot at height `h` to Talos's `trunc_sat` of the double. -/
theorem exec_truncSat {le : temp_env} {m : mem} {h : Nat} {x : UInt64}
    (hx : le[slotId h .f64]? = some (.Vfloat x)) :
    exec_stmt A X E.ge empty_env le m (truncSatStmt h) E0
      (le.insert (slotId h .i64) (.Vlong (IEEE64.truncSatI64U x))) m .Out_normal := by
  have hd : eval_expr A E.ge empty_env le m (tmp h .f64) (.Vfloat x) := .eval_Etempvar _ _ _ hx
  have hc1 : eval_expr A E.ge empty_env le m (.Ebinop .One (tmp h .f64) (tmp h .f64) tint)
      (Val.of_bool (IEEE64.isNaN x)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd hd (by
      show some (Val.of_bool (LClight.Float.cmp .Cne x x)) = _
      rw [cmp_ne_self])
  have hc2 : eval_expr A E.ge empty_env le m (.Ebinop .Ole (tmp h .f64) minusOne tint)
      (Val.of_bool (IEEE64.le x m1Bits)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd eval_minusOne (by
      show some (Val.of_bool (LClight.Float.cmp .Cle x m1Bits)) = _
      rw [cmp_le])
  have hc3 : eval_expr A E.ge empty_env le m (.Ebinop .Oge (tmp h .f64) twoTo64 tint)
      (Val.of_bool (IEEE64.le t64Bits x)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd (.eval_Econst_float _ _) (by
      show some (Val.of_bool (LClight.Float.cmp .Cge x t64Bits)) = _
      rw [cmp_ge])
  have hb : ∀ b : Bool, bool_val (Val.of_bool b) tint m = some b := by
    intro b; cases b <;> rfl
  unfold truncSatStmt
  cases hn : IEEE64.isNaN x
  · obtain ⟨h1, h2, h3⟩ := truncSat_cases x hn
    refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc1 (by rw [hn]; exact hb false) ?_
    cases hl : IEEE64.le x m1Bits
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc2 (by rw [hl]; exact hb false) ?_
      cases hg : IEEE64.le t64Bits x
      · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc3 (by rw [hg]; exact hb false) ?_
        refine .exec_Sset _ _ _ _ _ _ (.eval_Ecast _ _ _ _ hd ?_)
        show (match LClight.Float.to_longu x with
          | some i => some (val.Vlong i)
          | none => none) = _
        rw [h3 hl hg]
      · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc3 (by rw [hg]; exact hb true) ?_
        rw [h2 hl hg]
        exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc2 (by rw [hl]; exact hb true) ?_
      rw [h1 hl]
      exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc1 (by rw [hn]; exact hb true) ?_
    have : IEEE64.truncSatI64U x = 0 := by simp [IEEE64.truncSatI64U, hn]
    rw [this]
    exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)

theorem sim_i64TruncSatF64U (F : Nat) : InstrSim A X E mod c F .i64TruncSatF64U := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f64 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_exec hrest hinv.locals hinv.brk hb (exec_truncSat hx) (te_insert_same _ _ _) rfl
        (fun id hid _ => te_insert_ne _ (Ne.symm hid)) hinv.store hinv.status

end

end LeanExe.Native
