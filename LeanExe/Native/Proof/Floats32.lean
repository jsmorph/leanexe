import LeanExe.Native.Proof.Floats
import LeanExe.ProofKit.F32Bits
import LeanExe.ProofKit.F32Sign

/-!
The simulation of the binary32 forms other than `sqrt` and `nearest`, in the pattern of
`Floats.lean`.

Talos's `IEEE32` operations that round return the canonical NaN `0x7FC00000` whenever their
result is a NaN, which `F32Bits` gives through Lean's model of `Float32` (`canon32_add` and the
lemmas after it).  The Lean copy returns the same bits when the result is a number and some
quiet NaN otherwise (`canonOf32_binop`), so `canonStmt32` makes the C result Talos's for every
`Archi`.  The comparisons and the conversions from integers agree with Talos's by the
definitions of the copy.  A reinterpretation stores into the first four bytes of `lx_pun` at one
type and loads at the other, `abs` clears the sign bit of the word there, and the saturating
truncations follow Talos's case analysis through their three guards.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## Talos's NaN results -/

/-- `r`, with a NaN replaced by the canonical NaN. -/
def canonOf32 (r : UInt32) : UInt32 := if IEEE32.isNaN r then IEEE32.canonicalNaN else r

theorem canonOf32_float (x : _root_.Float32) : canonOf32 x.toBits = x.toBits :=
  LeanExe.ProofKit.F32Bits.toBits_canonical x

theorem toBits_ofBits32_num {w : UInt32} (h : IEEE32.isNaN w = false) :
    (_root_.Float32.ofBits w).toBits = w := by
  rw [LeanExe.ProofKit.F32Bits.toBits_ofBits, h]
  rfl

theorem canonOf32_canonical : canonOf32 IEEE32.canonicalNaN = IEEE32.canonicalNaN := by
  unfold canonOf32
  split <;> rfl

theorem canon32_add (a b : UInt32) : canonOf32 (IEEE32.add a b) = IEEE32.add a b := by
  cases ha : IEEE32.isNaN a
  · cases hb : IEEE32.isNaN b
    · rw [← toBits_ofBits32_num ha, ← toBits_ofBits32_num hb,
        ← LeanExe.ProofKit.F32Bits.toBits_add]
      exact canonOf32_float _
    · have : IEEE32.add a b = IEEE32.canonicalNaN := by simp [IEEE32.add, hb]
      rw [this, canonOf32_canonical]
  · have : IEEE32.add a b = IEEE32.canonicalNaN := by simp [IEEE32.add, ha]
    rw [this, canonOf32_canonical]

theorem canon32_sub (a b : UInt32) : canonOf32 (IEEE32.sub a b) = IEEE32.sub a b := by
  cases ha : IEEE32.isNaN a
  · cases hb : IEEE32.isNaN b
    · rw [← toBits_ofBits32_num ha, ← toBits_ofBits32_num hb,
        ← LeanExe.ProofKit.F32Bits.toBits_sub]
      exact canonOf32_float _
    · have : IEEE32.sub a b = IEEE32.canonicalNaN := by
        simp [IEEE32.sub, IEEE32.add, LeanExe.ProofKit.F32Sign.isNaN_negate, hb]
      rw [this, canonOf32_canonical]
  · have : IEEE32.sub a b = IEEE32.canonicalNaN := by simp [IEEE32.sub, IEEE32.add, ha]
    rw [this, canonOf32_canonical]

theorem canon32_mul (a b : UInt32) : canonOf32 (IEEE32.mul a b) = IEEE32.mul a b := by
  cases ha : IEEE32.isNaN a
  · cases hb : IEEE32.isNaN b
    · rw [← toBits_ofBits32_num ha, ← toBits_ofBits32_num hb,
        ← LeanExe.ProofKit.F32Bits.toBits_mul]
      exact canonOf32_float _
    · have : IEEE32.mul a b = IEEE32.canonicalNaN := by simp [IEEE32.mul, hb]
      rw [this, canonOf32_canonical]
  · have : IEEE32.mul a b = IEEE32.canonicalNaN := by simp [IEEE32.mul, ha]
    rw [this, canonOf32_canonical]

theorem canon32_div (a b : UInt32) : canonOf32 (IEEE32.div a b) = IEEE32.div a b := by
  cases ha : IEEE32.isNaN a
  · cases hb : IEEE32.isNaN b
    · rw [← toBits_ofBits32_num ha, ← toBits_ofBits32_num hb,
        ← LeanExe.ProofKit.F32Bits.toBits_div]
      exact canonOf32_float _
    · have : IEEE32.div a b = IEEE32.canonicalNaN := by simp [IEEE32.div, hb]
      rw [this, canonOf32_canonical]
  · have : IEEE32.div a b = IEEE32.canonicalNaN := by simp [IEEE32.div, ha]
    rw [this, canonOf32_canonical]

/-! ## The copy's NaN results -/

theorem isNaN_quiet_nan_32 (sp : Bool × Nat) : IEEE32.isNaN (quiet_nan_32 sp) = true := by
  have hq : (quiet_nan_32_payload sp.2).testBit 22 = true := by
    unfold quiet_nan_32_payload
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_two_pow_self]
    simp
  have hlt : quiet_nan_32_payload sp.2 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have hne : quiet_nan_32_payload sp.2 ≠ 0 := fun h => by simp [h] at hq
  have hv : (quiet_nan_32 sp).toNat =
      (if sp.1 then 2 ^ 31 else 0) + 0xFF * 2 ^ 23 + quiet_nan_32_payload sp.2 := by
    unfold quiet_nan_32
    rw [UInt32.toNat_ofNat']
    split <;> omega
  simp only [IEEE32.isNaN, IEEE32.exponent, IEEE32.fraction, hv, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq]
  split <;> omega

/-- The copy's result of an operation whose Talos result is `r`, canonicalized, is `r`
canonicalized. -/
theorem canonOf32_binop (A : Archi) (r x y : UInt32) :
    canonOf32 (LClight.Float32.binop A r x y) = canonOf32 r := by
  unfold LClight.Float32.binop canonOf32
  cases h : IEEE32.isNaN r
  · simp [h]
  · simp [LClight.Float32.binop_nan, isNaN_quiet_nan_32]

/-! ## Comparisons -/

theorem cmp32_ne_self (x : UInt32) : LClight.Float32.cmp .Cne x x = IEEE32.isNaN x := by
  unfold LClight.Float32.cmp LClight.Float32.compare
  cases h : IEEE32.isNaN x
  · simp [IEEE32.eq, h, cmp_of_comparison]
  · simp [cmp_of_comparison]

theorem cmp32_eq (x y : UInt32) : LClight.Float32.cmp .Ceq x y = IEEE32.eq x y := by
  unfold LClight.Float32.cmp LClight.Float32.compare
  split
  · rename_i h
    simp [IEEE32.eq, h, cmp_of_comparison]
  · split
    · rename_i _ he; simp [he, cmp_of_comparison]
    · rename_i _ he
      split <;> simp [cmp_of_comparison, he]

theorem cmp32_lt (x y : UInt32) : LClight.Float32.cmp .Clt x y = IEEE32.lt x y := by
  unfold LClight.Float32.cmp LClight.Float32.compare
  split
  · rename_i h
    simp [IEEE32.lt, h, cmp_of_comparison]
  · rename_i hn
    split
    · rename_i he
      simp only [IEEE32.eq, IEEE32.lt, Bool.or_eq_true, not_or] at hn he ⊢
      simp only [hn.1, hn.2, Bool.false_eq_true, or_self, ite_false, beq_iff_eq] at he ⊢
      simp [cmp_of_comparison, he]
    · rename_i hne
      split
      · rename_i hl; simp [cmp_of_comparison, hl]
      · rename_i hl; simp [cmp_of_comparison, Bool.eq_false_iff.mpr hl]

theorem cmp32_le (x y : UInt32) : LClight.Float32.cmp .Cle x y = IEEE32.le x y := by
  unfold LClight.Float32.cmp LClight.Float32.compare
  split
  · rename_i h
    simp [IEEE32.le, h, cmp_of_comparison]
  · rename_i hn
    simp only [Bool.or_eq_true, not_or] at hn
    have hn1 : IEEE32.isNaN x = false := Bool.eq_false_iff.mpr hn.1
    have hn2 : IEEE32.isNaN y = false := Bool.eq_false_iff.mpr hn.2
    split
    · rename_i he
      simp only [IEEE32.eq, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
        beq_iff_eq] at he
      simp [cmp_of_comparison, IEEE32.le, hn1, hn2, he]
    · rename_i hne
      simp only [IEEE32.eq, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
        beq_iff_eq] at hne
      split
      · rename_i hl
        simp only [IEEE32.lt, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
          decide_eq_true_eq] at hl
        simp [cmp_of_comparison, IEEE32.le, hn1, hn2]
        omega
      · rename_i hl
        simp only [IEEE32.lt, hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false,
          decide_eq_true_eq] at hl
        simp [cmp_of_comparison, IEEE32.le, hn1, hn2]
        omega

/-- `Cge` is the reverse of `Cle`. -/
theorem cmp32_ge (x y : UInt32) : LClight.Float32.cmp .Cge x y = IEEE32.le y x := by
  rw [← cmp32_le]
  unfold LClight.Float32.cmp LClight.Float32.compare
  by_cases hn : IEEE32.isNaN x = true ∨ IEEE32.isNaN y = true
  · rcases hn with hn | hn <;> simp [hn, cmp_of_comparison]
  · simp only [not_or] at hn
    have hn1 : IEEE32.isNaN x = false := Bool.eq_false_iff.mpr hn.1
    have hn2 : IEEE32.isNaN y = false := Bool.eq_false_iff.mpr hn.2
    simp only [hn1, hn2, Bool.or_false, Bool.false_eq_true, ite_false, IEEE32.eq, IEEE32.lt,
      beq_iff_eq, decide_eq_true_eq]
    by_cases h1 : IEEE32.scaledValue x = IEEE32.scaledValue y
    · simp [h1, cmp_of_comparison]
    · by_cases h2 : IEEE32.scaledValue x < IEEE32.scaledValue y
      · have h3 : ¬ IEEE32.scaledValue y = IEEE32.scaledValue x := fun e => h1 e.symm
        have h4 : ¬ IEEE32.scaledValue y < IEEE32.scaledValue x := by omega
        simp [h1, h2, h3, h4, cmp_of_comparison]
      · have h3 : ¬ IEEE32.scaledValue y = IEEE32.scaledValue x := fun e => h1 e.symm
        have h4 : IEEE32.scaledValue y < IEEE32.scaledValue x := by omega
        simp [h1, h2, h3, h4, cmp_of_comparison]

/-! ## The saturating truncations -/

/-- -1.0f. -/
def m1Bits32 : UInt32 := 0xBF800000
/-- 2^64 as a float. -/
def t64Bits32 : UInt32 := 0x5F800000
/-- 2^31 as a float. -/
def t31Bits32 : UInt32 := 0x4F000000
/-- -2^31 as a float. -/
def m31Bits32 : UInt32 := 0xCF000000

theorem sv32_m1 : IEEE32.scaledValue m1Bits32 = -(2 ^ 149 : Int) := by decide +kernel
theorem sv32_t64 : IEEE32.scaledValue t64Bits32 = (2 ^ 213 : Int) := by decide +kernel
theorem sv32_t31 : IEEE32.scaledValue t31Bits32 = (2 ^ 180 : Int) := by decide +kernel
theorem sv32_m31 : IEEE32.scaledValue m31Bits32 = -(2 ^ 180 : Int) := by decide +kernel

theorem mag32_inf (x : UInt32) (hf : IEEE32.isFinite x = false) :
    2 ^ 253 ≤ IEEE32.scaledMagnitude x := by
  simp only [IEEE32.isFinite, bne_eq_false_iff_eq] at hf
  unfold IEEE32.scaledMagnitude
  rw [hf]
  simp only [beq_iff_eq, show (255 : Nat) ≠ 0 from by decide, ite_false]
  calc 2 ^ 253 ≤ 2 ^ (255 - 1) := Nat.pow_le_pow_right (by decide) (by decide)
    _ ≤ (2 ^ 23 + IEEE32.fraction x) * 2 ^ (255 - 1) :=
      Nat.le_mul_of_pos_left _ (by have := Nat.one_le_two_pow (n := 23); omega)

/-- Talos's `i64.trunc_sat_f32_u` of a number, through the guards of `truncSat32UStmt`: 0 at or
below -1, the largest word at or above 2^64, and the C conversion between. -/
theorem truncSat32U_cases (x : UInt32) (hn : IEEE32.isNaN x = false) :
    (IEEE32.le x m1Bits32 = true → IEEE32.truncSatI64U x = 0) ∧
    (IEEE32.le x m1Bits32 = false → IEEE32.le t64Bits32 x = true →
      IEEE32.truncSatI64U x = 0xFFFFFFFFFFFFFFFF) ∧
    (IEEE32.le x m1Bits32 = false → IEEE32.le t64Bits32 x = false →
      LClight.Float32.to_longu x = some (IEEE32.truncSatI64U x)) := by
  have hm1n : IEEE32.isNaN m1Bits32 = false := by decide
  have htn : IEEE32.isNaN t64Bits32 = false := by decide
  have hle1 : IEEE32.le x m1Bits32 = decide (IEEE32.scaledValue x ≤ -(2 ^ 149 : Int)) := by
    simp [IEEE32.le, hn, hm1n, sv32_m1]
  have hle2 : IEEE32.le t64Bits32 x = decide ((2 ^ 213 : Int) ≤ IEEE32.scaledValue x) := by
    simp [IEEE32.le, hn, htn, sv32_t64]
  rw [hle1, hle2]
  have hinf := mag32_inf x
  unfold IEEE32.truncSatI64U LClight.Float32.to_longu LClight.Float32.ZofB_range
    IEEE32.truncatedInt
  unfold IEEE32.scaledValue
  simp only [hn, Bool.false_eq_true, ite_false]
  generalize IEEE32.scaledMagnitude x = M at *
  have hP : (0 : Int) < 2 ^ 149 := by positivity
  have h0 : (0 : Int) ≤ (M : Int) / 2 ^ 149 := Int.ediv_nonneg (by omega) hP.le
  have hlt : M < 2 ^ 213 → (M : Int) / 2 ^ 149 < 2 ^ 64 := fun h =>
    Int.ediv_lt_of_lt_mul hP (by
      have : ((2 : Int) ^ 64 * 2 ^ 149) = 2 ^ 213 := by rw [← pow_add]
      push_cast [this] at h ⊢; omega)
  have hge : 2 ^ 213 ≤ M → (2 : Int) ^ 64 ≤ (M : Int) / 2 ^ 149 := fun h =>
    Int.le_ediv_of_mul_le hP (by
      have : ((2 : Int) ^ 64 * 2 ^ 149) = 2 ^ 213 := by rw [← pow_add]
      rw [this]; exact_mod_cast h)
  have hz : M < 2 ^ 149 → (M : Int) / 2 ^ 149 = 0 := fun h =>
    Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast h)
  have hpos : 2 ^ 149 ≤ M → (1 : Int) ≤ (M : Int) / 2 ^ 149 := fun h =>
    Int.le_ediv_of_mul_le hP (by rw [one_mul]; exact_mod_cast h)
  have hnat : ((M / 2 ^ 149 : Nat) : Int) = (M : Int) / 2 ^ 149 := by push_cast; rfl
  have hmax : Int64.max_unsigned = 2 ^ 64 - 1 := rfl
  cases hs : IEEE32.sign x <;> cases hfin : IEEE32.isFinite x <;>
    simp only [hfin, hnat, Bool.false_eq_true, ite_false, ite_true] at hinf ⊢
  all_goals
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le, true_implies] at *
    generalize hq : (M : Int) / 2 ^ 149 = q at *
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
        · unfold Int64.repr IEEE32.intToUInt64
          rw [ite_eq_right (by omega), Int64.modulus, Int.emod_eq_of_lt (by omega) (by omega)]
          congr 1
          omega
  -- negative, infinite
  · exact ⟨fun _ => trivial, fun _ h => by omega, fun h _ => by omega⟩
  -- negative, finite
  · refine ⟨fun h => ?_, fun _ h => by omega, fun h _ => ?_⟩
    · have := hpos (by exact_mod_cast (by omega : (2 : Int) ^ 149 ≤ M))
      rw [ite_eq_left (by omega)]
    · have hq0 := hz (by exact_mod_cast (by omega : (M : Int) < 2 ^ 149))
      subst hq0
      rw [ite_eq_left (show 0 ≤ -(0 : Int) ∧ -(0 : Int) ≤ Int64.max_unsigned from
        ⟨by omega, by rw [hmax]; omega⟩), Option.map_some, ite_eq_left (by omega)]
      rfl

/-- Talos's `i32.trunc_sat_f32_s` of a number, through the guards of `truncSat32SStmt`:
`0x80000000` at or below -2^31, `0x7FFFFFFF` at or above 2^31, and the C conversion to `int`
between. -/
theorem truncSat32S_cases (x : UInt32) (hn : IEEE32.isNaN x = false) :
    (IEEE32.le x m31Bits32 = true → IEEE32.truncSatI32S x = 0x80000000) ∧
    (IEEE32.le x m31Bits32 = false → IEEE32.le t31Bits32 x = true →
      IEEE32.truncSatI32S x = 0x7FFFFFFF) ∧
    (IEEE32.le x m31Bits32 = false → IEEE32.le t31Bits32 x = false →
      LClight.Float32.to_int x = some (IEEE32.truncSatI32S x)) := by
  have hm1n : IEEE32.isNaN m31Bits32 = false := by decide
  have htn : IEEE32.isNaN t31Bits32 = false := by decide
  have hle1 : IEEE32.le x m31Bits32 = decide (IEEE32.scaledValue x ≤ -(2 ^ 180 : Int)) := by
    simp [IEEE32.le, hn, hm1n, sv32_m31]
  have hle2 : IEEE32.le t31Bits32 x = decide ((2 ^ 180 : Int) ≤ IEEE32.scaledValue x) := by
    simp [IEEE32.le, hn, htn, sv32_t31]
  rw [hle1, hle2]
  have hinf := mag32_inf x
  unfold IEEE32.truncSatI32S LClight.Float32.to_int LClight.Float32.ZofB_range
    IEEE32.truncatedInt
  unfold IEEE32.scaledValue
  simp only [hn, Bool.false_eq_true, ite_false]
  generalize IEEE32.scaledMagnitude x = M at *
  have hP : (0 : Int) < 2 ^ 149 := by positivity
  have h0 : (0 : Int) ≤ (M : Int) / 2 ^ 149 := Int.ediv_nonneg (by omega) hP.le
  have hlt : M < 2 ^ 180 → (M : Int) / 2 ^ 149 < 2 ^ 31 := fun h =>
    Int.ediv_lt_of_lt_mul hP (by
      have : ((2 : Int) ^ 31 * 2 ^ 149) = 2 ^ 180 := by rw [← pow_add]
      push_cast [this] at h ⊢; omega)
  have hge : 2 ^ 180 ≤ M → (2 : Int) ^ 31 ≤ (M : Int) / 2 ^ 149 := fun h =>
    Int.le_ediv_of_mul_le hP (by
      have : ((2 : Int) ^ 31 * 2 ^ 149) = 2 ^ 180 := by rw [← pow_add]
      rw [this]; exact_mod_cast h)
  have hnat : ((M / 2 ^ 149 : Nat) : Int) = (M : Int) / 2 ^ 149 := by push_cast; rfl
  have hmin : LClight.Int.min_signed = -2 ^ 31 := rfl
  have hmax : LClight.Int.max_signed = 2 ^ 31 - 1 := rfl
  cases hs : IEEE32.sign x <;> cases hfin : IEEE32.isFinite x <;>
    simp only [hfin, hnat, Bool.false_eq_true, ite_false, ite_true] at hinf ⊢
  all_goals
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_le, true_implies] at *
    generalize hq : (M : Int) / 2 ^ 149 = q at *
  -- positive, infinite
  · exact ⟨fun h => by omega, fun _ _ => trivial, fun _ h => by omega⟩
  -- positive, finite
  · refine ⟨fun h => by omega, fun _ h => ?_, fun _ h => ?_⟩
    · have := hge (by exact_mod_cast h)
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    · have hq1 := hlt (by exact_mod_cast h)
      rw [ite_eq_left (show LClight.Int.min_signed ≤ q ∧ q ≤ LClight.Int.max_signed from
        ⟨by rw [hmin]; omega, by rw [hmax]; omega⟩), Option.map_some, ite_eq_right (by omega)]
      congr 1
      split
      · obtain rfl : q = 2 ^ 31 - 1 := by omega
        decide +kernel
      · unfold LClight.Int.repr IEEE32.intToUInt32
        rw [ite_eq_right (by omega), LClight.Int.modulus, Int.emod_eq_of_lt (by omega) (by omega)]
        congr 1
        omega
  -- negative, infinite
  · exact ⟨fun _ => trivial, fun _ h => by omega, fun h _ => by omega⟩
  -- negative, finite
  · refine ⟨fun h => ?_, fun _ h => by omega, fun h _ => ?_⟩
    · have := hge (by exact_mod_cast (by omega : 2 ^ 180 ≤ M))
      rw [ite_eq_left (by omega)]
    · have hq1 := hlt (by exact_mod_cast (by omega : (M : Int) < 2 ^ 180))
      rw [ite_eq_left (show LClight.Int.min_signed ≤ -q ∧ -q ≤ LClight.Int.max_signed from
        ⟨by rw [hmin]; omega, by rw [hmax]; omega⟩), Option.map_some, ite_eq_right (by omega),
        ite_eq_right (by omega)]
      congr 1
      unfold LClight.Int.repr IEEE32.intToUInt32
      by_cases hq0 : q = 0
      · subst hq0; decide
      · rw [ite_eq_left (by omega), LClight.Int.modulus,
          Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
        congr 1
        omega

/-! ## Negation of a constant -/

theorem negate32_negate (v : UInt32) : IEEE32.negate (IEEE32.negate v) = v := by
  obtain ⟨he, hf, hs⟩ := LeanExe.ProofKit.F32Sign.fields_negate v
  show IEEE32.encodeFinite (!IEEE32.sign (IEEE32.negate v)) (IEEE32.exponent (IEEE32.negate v))
    (IEEE32.fraction (IEEE32.negate v)) = v
  rw [he, hf, hs, Bool.not_not, LeanExe.ProofKit.F32Packing.encode_fields]

/-! ## Values on the stack -/

theorem has_f32 {v : Value} (h : VT.has .f32 v = true) : ∃ x, v = .f32 x := by
  cases v <;> simp_all [VT.has]

theorem pop1_f32 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.f32 :: σr) vs) :
    ∃ x vr, vs = .f32 x :: vr ∧ le[slotId σr.length .f32]? = some (.Vsingle x) ∧
      StackRel le σr vr := by
  obtain ⟨v1, vr, rfl, h1, hl1, hrest⟩ := h.cons_inv
  obtain ⟨x, rfl⟩ := has_f32 h1
  exact ⟨x, vr, rfl, hl1, hrest⟩

theorem pop2_f32 {le : temp_env} {σr : List VT} {vs : List Value}
    (h : StackRel le (.f32 :: .f32 :: σr) vs) :
    ∃ y x vr, vs = .f32 y :: .f32 x :: vr ∧
      le[slotId (σr.length + 1) .f32]? = some (.Vsingle y) ∧
      le[slotId σr.length .f32]? = some (.Vsingle x) ∧ StackRel le σr vr := by
  obtain ⟨v1, vs1, rfl, h1, hl1, h'⟩ := h.cons_inv
  obtain ⟨v2, vr, rfl, h2, hl2, hrest⟩ := h'.cons_inv
  obtain ⟨y, rfl⟩ := has_f32 h1
  obtain ⟨x, rfl⟩ := has_f32 h2
  exact ⟨y, x, vr, rfl, hl1, hl2, hrest⟩

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-! ## The first four bytes of `lx_pun` -/

theorem pun_valid32 {α : Type} {st : Store α} {m : mem} (hst : StoreRel E st m)
    {chunk : memory_chunk} (hc : size_chunk chunk = 4) (ha : align_chunk chunk = 4) :
    Mem.valid_access m chunk E.pun 0 .Writable :=
  Mem.valid_access_four hst.2.punW hc ha

theorem eval_punAt_single (hE : EnvOk E) {le : temp_env} {m : mem} {x : UInt32}
    (hl : Mem.load .Mfloat32 m E.pun 0 = some (.Vsingle x)) :
    eval_expr A E.ge empty_env le m (punAt tfloat) (.Vsingle x) :=
  .eval_Elvalue _ _ _ _ _ (eval_punAt_lvalue hE le m _)
    (.deref_loc_value .Mfloat32 _ rfl (by rw [loadv_zero _ _ _ (by decide)]; exact hl))

theorem eval_punAt_int (hE : EnvOk E) {le : temp_env} {m : mem} {x : UInt32}
    (hl : Mem.load .Mint32 m E.pun 0 = some (.Vint x)) :
    eval_expr A E.ge empty_env le m (punAt tuint) (.Vint x) :=
  .eval_Elvalue _ _ _ _ _ (eval_punAt_lvalue hE le m _)
    (.deref_loc_value .Mint32 _ rfl (by rw [loadv_zero _ _ _ (by decide)]; exact hl))

theorem exec_punAssign_int (hE : EnvOk E) {le : temp_env} {m : mem} {e : expr} {x : UInt32}
    (he : eval_expr A E.ge empty_env le m e (.Vint x)) (hty : typeof e = tuint)
    (hva : Mem.valid_access m .Mint32 E.pun 0 .Writable) :
    exec_stmt A X E.ge empty_env le m (.Sassign (punAt tuint) e) E0 le
      (Mem.stored .Mint32 m E.pun 0 (.Vint x)) .Out_normal :=
  .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ (eval_punAt_lvalue hE le m _) he (by rw [hty]; rfl)
    (.assign_loc_value _ .Mint32 _ rfl
      (by rw [storev_zero _ _ _ _ (by decide)]; exact Mem.store_ok _ hva))

theorem exec_punAssign_single (hE : EnvOk E) {le : temp_env} {m : mem} {e : expr} {x : UInt32}
    (he : eval_expr A E.ge empty_env le m e (.Vsingle x)) (hty : typeof e = tfloat)
    (hva : Mem.valid_access m .Mfloat32 E.pun 0 .Writable) :
    exec_stmt A X E.ge empty_env le m (.Sassign (punAt tfloat) e) E0 le
      (Mem.stored .Mfloat32 m E.pun 0 (.Vsingle x)) .Out_normal :=
  .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ (eval_punAt_lvalue hE le m _) he (by rw [hty]; rfl)
    (.assign_loc_value _ .Mfloat32 _ rfl
      (by rw [storev_zero _ _ _ _ (by decide)]; exact Mem.store_ok _ hva))

/-- `punStore32 w h`: the float slot at height `h` gets the bits of the word `w`. -/
theorem exec_punStore32 (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} {m : mem}
    {e : expr} {x : UInt32} {h : Nat} (he : eval_expr A E.ge empty_env le m e (.Vint x))
    (hty : typeof e = tuint) (hst : StoreRel E st m) :
    exec_stmt A X E.ge empty_env le m (punStore32 e h) E0
      (le.insert (slotId h .f32) (.Vsingle x)) (Mem.stored .Mint32 m E.pun 0 (.Vint x))
      .Out_normal :=
  .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (exec_punAssign_int hE he hty (pun_valid32 hst rfl rfl))
    (.exec_Sset _ _ _ _ _ _ (eval_punAt_single hE
      (Mem.load_single_stored_int _ _ _ _ (pun_valid32 hst rfl rfl))))

/-- `punBits32 h k`: the word slot at height `k` gets the bits of the float at height `h`. -/
theorem exec_punBits32 (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} {m : mem}
    {x : UInt32} {h k : Nat} (hx : le[slotId h .f32]? = some (.Vsingle x))
    (hst : StoreRel E st m) :
    exec_stmt A X E.ge empty_env le m (punBits32 h k) E0
      (le.insert (slotId k .i32) (.Vint x)) (Mem.stored .Mfloat32 m E.pun 0 (.Vsingle x))
      .Out_normal :=
  .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
    (exec_punAssign_single hE (.eval_Etempvar _ _ _ hx) rfl (pun_valid32 hst rfl rfl))
    (.exec_Sset _ _ _ _ _ _ (eval_punAt_int hE
      (Mem.load_int_stored_single _ _ _ _ (pun_valid32 hst rfl rfl))))

/-- `canonStmt32 h` replaces a NaN in the float slot at height `h` by the canonical NaN. -/
theorem exec_canon32 (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} {m : mem}
    {h : Nat} {q : UInt32} (hq : le[slotId h .f32]? = some (.Vsingle q)) (hst : StoreRel E st m)
    (hs : StatusRel E m 0) :
    ∃ le' m', exec_stmt A X E.ge empty_env le m (canonStmt32 h) E0 le' m' .Out_normal ∧
      le'[slotId h .f32]? = some (.Vsingle (canonOf32 q)) ∧
      (∀ id, id ≠ slotId h .f32 → le'[id]? = le[id]?) ∧ StoreRel E st m' ∧
      StatusRel E m' 0 := by
  have hc : eval_expr A E.ge empty_env le m (.Ebinop .One (tmp h .f32) (tmp h .f32) tint)
      (Val.of_bool (IEEE32.isNaN q)) := by
    refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hq) (.eval_Etempvar _ _ _ hq) ?_
    show some (Val.of_bool (LClight.Float32.cmp .Cne q q)) = _
    rw [cmp32_ne_self]
  cases hn : IEEE32.isNaN q
  · refine ⟨le, m, ?_, ?_, fun _ _ => rfl, hst, hs⟩
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc ?_ (.exec_Sskip _ _ _)
      rw [hn]; rfl
    · rw [hq]; simp [canonOf32, hn]
  · refine ⟨le.insert (slotId h .f32) (.Vsingle IEEE32.canonicalNaN),
      Mem.stored .Mint32 m E.pun 0 (.Vint IEEE32.canonicalNaN), ?_, ?_,
      fun id hid => te_insert_ne _ (Ne.symm hid), hst.store_pun hE _ _, hs.store_pun hE _ _⟩
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc ?_
        (exec_punStore32 hE (.eval_Econst_int _ _) rfl hst)
      rw [hn]; rfl
    · rw [te_insert_same]; simp [canonOf32, hn]

end

/-! ## The forms -/

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- A binary32 operation that rounds. -/
theorem sim_ff32 (hE : EnvOk E) (F : Nat) (inst : Instruction) (op : binary_operation)
    (f : UInt32 → UInt32 → UInt32)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .f32 :: .f32 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.f32 :: σr) ∧
        s = .Ssequence (.Sset (slotId σr.length .f32)
          (.Ebinop op (tmp σr.length .f32) (tmp (σr.length + 1) .f32) tfloat))
          (canonStmt32 σr.length))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .f32 y :: .f32 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        .Fallthrough st { params := sl.params, locals := sl.locals, values := .f32 (f x y) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, ∃ q, sem_binary_operation A op (.Vsingle x) tfloat (.Vsingle y) tfloat m =
      some (.Vsingle q) ∧ canonOf32 q = f x y) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_f32 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      obtain ⟨q, hq, hqf⟩ := hsem m x y
      have h1 : exec_stmt A X E.ge empty_env le m (.Sset (slotId σr.length .f32)
          (.Ebinop op (tmp σr.length .f32) (tmp (σr.length + 1) .f32) tfloat)) E0
          (le.insert (slotId σr.length .f32) (.Vsingle q)) m .Out_normal :=
        .exec_Sset _ _ _ _ _ _
          (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx) (.eval_Etempvar _ _ _ hy) hq)
      obtain ⟨le2, m2, h2, hslot, hk, hst2, hs2⟩ := exec_canon32 (A := A) (X := X) hE
        (te_insert_same le _ _) hinv.store hinv.status
      exact push_exec hrest hinv.locals hinv.brk hb (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2)
        (by rw [hslot, hqf]; rfl) rfl
        (fun id hid _ => by rw [hk id hid, te_insert_ne _ (Ne.symm hid)]) hst2 hs2

theorem tr_ff32 {inst : Instruction} {op : binary_operation} (hop : f32Op inst = some op)
    {L : List Label} {σ : List VT} {n : Nat} {s : statement} {σ' : Option (List VT)} {n' : Nat}
    (h : trInstr c L σ n inst = some (s, σ', n')) :
    ∃ σr, σ = .f32 :: .f32 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧ σ' = some (.f32 :: σr) ∧
      s = .Ssequence (.Sset (slotId σr.length .f32)
        (.Ebinop op (tmp σr.length .f32) (tmp (σr.length + 1) .f32) tfloat))
        (canonStmt32 σr.length) := by
  have hinst : inst = .f32Add ∨ inst = .f32Sub ∨ inst = .f32Mul ∨ inst = .f32Div := by
    cases inst <;> simp [f32Op] at hop ⊢
  rcases hinst with rfl | rfl | rfl | rfl <;>
  · simp only [f32Op, Option.some.injEq] at hop
    subst hop
    rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
      simp [trInstr, f32Op, pops, Option.bind_eq_some_iff] at h
    obtain ⟨hb, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
    exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩

theorem sim_f32Add (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Add :=
  sim_ff32 hE F .f32Add .Oadd f32Add (fun _ _ _ _ _ _ h => tr_ff32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf32 (LClight.Float32.binop A (IEEE32.add x y) x y) = _
      rw [canonOf32_binop, canon32_add]; rfl⟩)

theorem sim_f32Sub (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Sub :=
  sim_ff32 hE F .f32Sub .Osub f32Sub (fun _ _ _ _ _ _ h => tr_ff32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf32 (LClight.Float32.binop A (IEEE32.sub x y) x y) = _
      rw [canonOf32_binop, canon32_sub]; rfl⟩)

theorem sim_f32Mul (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Mul :=
  sim_ff32 hE F .f32Mul .Omul f32Mul (fun _ _ _ _ _ _ h => tr_ff32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf32 (LClight.Float32.binop A (IEEE32.mul x y) x y) = _
      rw [canonOf32_binop, canon32_mul]; rfl⟩)

theorem sim_f32Div (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Div :=
  sim_ff32 hE F .f32Div .Odiv f32Div (fun _ _ _ _ _ _ h => tr_ff32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => ⟨_, rfl, by
      show canonOf32 (LClight.Float32.binop A (IEEE32.div x y) x y) = _
      rw [canonOf32_binop, canon32_div]; rfl⟩)

/-- A binary32 comparison. -/
theorem sim_fcmp32 (F : Nat) (inst : Instruction) (op : binary_operation)
    (f : UInt32 → UInt32 → Bool)
    (htr : ∀ L σ n s σ' n', trInstr c L σ n inst = some (s, σ', n') →
      ∃ σr, σ = .f32 :: .f32 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧
        σ' = some (.i32 :: σr) ∧
        s = .Sset (slotId σr.length .i32)
          (.Ecast (.Ebinop op (tmp σr.length .f32) (tmp (σr.length + 1) .f32) tint) tuint))
    (htalos : ∀ (f' : Nat) {α : Type} (st : Store α) (sl : Locals) env x y vr,
      sl.values = .f32 y :: .f32 x :: vr →
      execOne (f' + 1) mod st sl inst env =
        .Fallthrough st
          { params := sl.params, locals := sl.locals, values := .i32 (if f x y then 1 else 0) :: vr })
    (hzero : ∀ {α : Type} (st : Store α) (sl : Locals) env,
      execOne 0 mod st sl inst env = .OutOfFuel)
    (hsem : ∀ m x y, sem_binary_operation A op (.Vsingle x) tfloat (.Vsingle y) tfloat m =
      some (Val.of_bool (f x y))) :
    InstrSim A X E mod c F inst := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  obtain ⟨σr, rfl, hb, rfl, rfl, rfl⟩ := htr L σ n s σ' n' h
  cases F with
  | zero => rw [hzero]; trivial
  | succ f' =>
      obtain ⟨y, x, vr, hvs, hy, hx, hrest⟩ := pop2_f32 hinv.stack
      rw [htalos f' st sl env x y vr hvs]
      refine push_step hrest hinv.locals hinv.store hinv.status hinv.brk ?_ rfl hb
      refine .eval_Ecast _ _ _ _ (.eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ hx)
        (.eval_Etempvar _ _ _ hy) (hsem m x y)) ?_
      rw [of_bool_eq]
      exact cast_int_uint m _

theorem tr_fcmp32 {inst : Instruction} {op : binary_operation} (hop : f32Cmp inst = some op)
    {L : List Label} {σ : List VT} {n : Nat} {s : statement} {σ' : Option (List VT)} {n' : Nat}
    (h : trInstr c L σ n inst = some (s, σ', n')) :
    ∃ σr, σ = .f32 :: .f32 :: σr ∧ curBase L ≤ σr.length ∧ n' = n ∧ σ' = some (.i32 :: σr) ∧
      s = .Sset (slotId σr.length .i32)
        (.Ecast (.Ebinop op (tmp σr.length .f32) (tmp (σr.length + 1) .f32) tint) tuint) := by
  have hinst : inst = .f32Eq ∨ inst = .f32Lt ∨ inst = .f32Le := by
    cases inst <;> simp [f32Cmp] at hop ⊢
  rcases hinst with rfl | rfl | rfl <;>
  · simp only [f32Cmp, Option.some.injEq] at hop
    subst hop
    rcases σ with _ | ⟨a, _ | ⟨b, σr⟩⟩ <;>
      simp [trInstr, f32Cmp, pops, Option.bind_eq_some_iff] at h
    obtain ⟨hb, ⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
    exact ⟨σr, rfl, hb, rfl, rfl, rfl⟩

theorem sim_f32Eq (F : Nat) : InstrSim A X E mod c F .f32Eq :=
  sim_fcmp32 F .f32Eq .Oeq f32Eq (fun _ _ _ _ _ _ h => tr_fcmp32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => by
      show some (Val.of_bool (LClight.Float32.cmp .Ceq x y)) = _
      rw [cmp32_eq]; rfl)

theorem sim_f32Lt (F : Nat) : InstrSim A X E mod c F .f32Lt :=
  sim_fcmp32 F .f32Lt .Olt f32Lt (fun _ _ _ _ _ _ h => tr_fcmp32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => by
      show some (Val.of_bool (LClight.Float32.cmp .Clt x y)) = _
      rw [cmp32_lt]; rfl)

theorem sim_f32Le (F : Nat) : InstrSim A X E mod c F .f32Le :=
  sim_fcmp32 F .f32Le .Ole f32Le (fun _ _ _ _ _ _ h => tr_fcmp32 rfl h)
    (fun _ _ st sl env x y vr hvs => by simp only [execOne.eq_def, hvs])
    (fun st sl env => by simp only [execOne.eq_def])
    (fun m x y => by
      show some (Val.of_bool (LClight.Float32.cmp .Cle x y)) = _
      rw [cmp32_le]; rfl)

theorem int64_unsigned_eq (x : UInt64) : LClight.Int64.unsigned x = (x.toNat : _root_.Int) := rfl

theorem int_signed_eq (x : UInt32) : LClight.Int.signed x = IEEE32.signedI32Value x := by
  have hu : LClight.Int.unsigned x = (x.toNat : _root_.Int) := rfl
  have hh : LClight.Int.half_modulus = 2 ^ 31 := rfl
  have hm : LClight.Int.modulus = 2 ^ 32 := rfl
  unfold LClight.Int.signed IEEE32.signedI32Value IEEE32.sign
  rw [hu, hh, hm]
  by_cases h : 2 ^ 31 ≤ x.toNat
  · rw [ite_eq_right (by omega), decide_eq_true h, ite_eq_left rfl]
  · rw [ite_eq_left (by omega), decide_eq_false h, ite_eq_right (by decide)]

theorem sim_f32ConvertI64U (F : Nat) : InstrSim A X E mod c F .f32ConvertI64U := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i64 hinv.stack
      simp only [execOne.eq_def, hvs]
      refine push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hx) ?_) rfl hb
      show some (val.Vsingle (LClight.Float32.of_longu x)) = some (val.Vsingle (f32ConvertI64U x))
      simp only [LClight.Float32.of_longu, int64_unsigned_eq, f32ConvertI64U, IEEE32.convertI64U]

theorem sim_f32ConvertI32S (F : Nat) : InstrSim A X E mod c F .f32ConvertI32S := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      have hc : sem_cast (.Vint x) tuint tint m = some (.Vint x) := rfl
      refine push_step hrest hinv.locals hinv.store hinv.status hinv.brk
        (.eval_Ecast _ _ (.Vint x) _ (.eval_Ecast _ _ _ _ (.eval_Etempvar _ _ _ hx) hc) ?_) rfl hb
      show some (val.Vsingle (LClight.Float32.of_int x)) = some (val.Vsingle (f32ConvertI32S x))
      simp only [LClight.Float32.of_int, int_signed_eq, f32ConvertI32S, IEEE32.convertI32S]

theorem sim_f32ReinterpretI32 (hE : EnvOk E) (F : Nat) :
    InstrSim A X E mod c F .f32ReinterpretI32 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_i32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_exec hrest hinv.locals hinv.brk hb
        (exec_punStore32 hE (.eval_Etempvar _ _ _ hx) rfl hinv.store) (te_insert_same _ _ _) rfl
        (fun id hid _ => te_insert_ne _ (Ne.symm hid)) (hinv.store.store_pun hE _ _)
        (hinv.status.store_pun hE _ _)

theorem sim_i32ReinterpretF32 (hE : EnvOk E) (F : Nat) :
    InstrSim A X E mod c F .i32ReinterpretF32 := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_exec hrest hinv.locals hinv.brk hb (exec_punBits32 hE hx hinv.store)
        (te_insert_same _ _ _) rfl
        (fun id hid _ => te_insert_ne _ (Ne.symm hid)) (hinv.store.store_pun hE _ _)
        (hinv.status.store_pun hE _ _)

theorem sim_f32Const (hE : EnvOk E) (F : Nat) (v : UInt32) :
    InstrSim A X E mod c F (.f32Const v) := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  simp [trInstr] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      simp only [execOne.eq_def]
      unfold f32ConstStmt
      split
      · split
        · refine push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk ?_ rfl hbase
          refine .eval_Eunop _ _ _ _ _ (.eval_Econst_single _ _) ?_
          show some (val.Vsingle (IEEE32.negate (IEEE32.negate v))) = _
          rw [negate32_negate]; rfl
        · exact push_step hinv.stack hinv.locals hinv.store hinv.status hinv.brk
            (.eval_Econst_single _ _) rfl hbase
      · exact push_exec hinv.stack hinv.locals hinv.brk hbase
          (exec_punStore32 hE (.eval_Econst_int _ _) rfl hinv.store) (te_insert_same _ _ _) rfl
          (fun id hid _ => te_insert_ne _ (Ne.symm hid)) (hinv.store.store_pun hE _ _)
          (hinv.status.store_pun hE _ _)

theorem abs_mask (x : UInt32) : x &&& UInt32.ofNat 0x7FFFFFFF = IEEE32.abs x := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and]
  have h1 : (UInt32.ofNat 0x7FFFFFFF).toNat = 2 ^ 31 - 1 := rfl
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]
  unfold IEEE32.abs IEEE32.encodeFinite IEEE32.exponent IEEE32.fraction
  rw [UInt32.toNat_ofNat']
  simp only [Bool.false_eq_true, ite_false, zero_add]
  have := x.toNat_lt
  omega

/-- A statement that sets the slot at height `σr.length` to `v` of type `t`, may change other
slots at that height and above, and keeps the locals and `brk`, in a memory related to the store
with `lx_status` 0. -/
theorem push_exec_scratch {L : List Label} {σr : List VT} {α : Type} {st : Store α}
    {sl : Locals} {le le' : temp_env} {m m' : mem} {s : statement} {v : Value} {t : VT}
    {vr : List Value}
    (hrest : StackRel le σr vr) (hloc : LocalsRel le c.locals (sl.params ++ sl.locals))
    (hb : le[brkId]? = some (.Vint 0)) (hbase : curBase L ≤ σr.length)
    (hx : exec_stmt A X E.ge empty_env le m s E0 le' m' .Out_normal)
    (hslot : le'[slotId σr.length t]? = some (cval v)) (ht : t.has v = true)
    (hfr : Frame σr.length le le') (hl : ∀ i, le'[localId i]? = le[localId i]?)
    (hk : le'[brkId]? = le[brkId]?) (hg : StoreRel E st m') (hs : StatusRel E m' 0) :
    Outcome A X E c L (some (t :: σr))
      (.Fallthrough st { params := sl.params, locals := sl.locals, values := v :: vr }) s le m := by
  refine ⟨t :: σr, rfl, by simp; omega, E0, le', m', hx, ?_, hfr.mono hbase⟩
  exact { stack := ⟨ht, hslot, hrest.frame hfr⟩
          locals := ⟨hloc.1, fun i hi => by
            obtain ⟨w, hw, htw, hl'⟩ := hloc.2 i hi
            exact ⟨w, hw, htw, by rw [hl i]; exact hl'⟩⟩
          store := hg
          status := hs
          brk := by rw [hk]; exact hb }

theorem sim_f32Abs (hE : EnvOk E) (F : Nat) : InstrSim A X E mod c F .f32Abs := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f32 hinv.stack
      simp only [execOne.eq_def, hvs]
      have h1 := exec_punBits32 (A := A) (X := X) (k := σr.length) hE hx hinv.store
      have hst1 := hinv.store.store_pun hE .Mfloat32 (.Vsingle x)
      have hs1 := hinv.status.store_pun hE .Mfloat32 (.Vsingle x)
      have he : eval_expr A E.ge empty_env (le.insert (slotId σr.length .i32) (.Vint x))
          (Mem.stored .Mfloat32 m E.pun 0 (.Vsingle x))
          (.Ebinop .Oand (tmp σr.length .i32) (cint 0x7FFFFFFF) tuint)
          (.Vint (IEEE32.abs x)) := by
        refine .eval_Ebinop _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _))
          (.eval_Econst_int _ _) ?_
        show sem_binary_operation A .Oand (.Vint x) tuint (.Vint (UInt32.ofNat 0x7FFFFFFF)) tuint
          (Mem.stored .Mfloat32 m E.pun 0 (.Vsingle x)) = _
        rw [sem_and_ii, abs_mask]
      have h2 := exec_punStore32 (A := A) (X := X) (h := σr.length) hE he rfl hst1
      exact push_exec_scratch hrest hinv.locals hinv.brk hb
        (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 h2) (te_insert_same _ _ _) rfl
        ((Frame.insert_slot _ _ _ _ (Nat.le_refl _)).trans
          (Frame.insert_slot _ _ _ _ (Nat.le_refl _)))
        (fun i => by
          rw [te_insert_ne _ (slotId_ne_localId _ _ i), te_insert_ne _ (slotId_ne_localId _ _ i)])
        (by rw [te_insert_ne _ (slotId_ne_brkId _ _), te_insert_ne _ (slotId_ne_brkId _ _)])
        (hst1.store_pun hE _ _) (hs1.store_pun hE _ _)

theorem eval_minusOne32 {le : temp_env} {m : mem} :
    eval_expr A E.ge empty_env le m minusOne32 (.Vsingle m1Bits32) :=
  .eval_Eunop _ _ _ _ _ (.eval_Econst_single _ _) rfl

theorem eval_minusTwo31f {le : temp_env} {m : mem} :
    eval_expr A E.ge empty_env le m minusTwo31f (.Vsingle m31Bits32) :=
  .eval_Eunop _ _ _ _ _ (.eval_Econst_single _ _) rfl

theorem bool_of_bool (m : mem) (b : Bool) : bool_val (Val.of_bool b) tint m = some b := by
  cases b <;> rfl

/-- `truncSat32UStmt h` sets the `i64` slot at height `h` to Talos's `i64.trunc_sat_f32_u` of
the float. -/
theorem exec_truncSat32U {le : temp_env} {m : mem} {h : Nat} {x : UInt32}
    (hx : le[slotId h .f32]? = some (.Vsingle x)) :
    exec_stmt A X E.ge empty_env le m (truncSat32UStmt h) E0
      (le.insert (slotId h .i64) (.Vlong (IEEE32.truncSatI64U x))) m .Out_normal := by
  have hd : eval_expr A E.ge empty_env le m (tmp h .f32) (.Vsingle x) := .eval_Etempvar _ _ _ hx
  have hc1 : eval_expr A E.ge empty_env le m (.Ebinop .One (tmp h .f32) (tmp h .f32) tint)
      (Val.of_bool (IEEE32.isNaN x)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd hd (by
      show some (Val.of_bool (LClight.Float32.cmp .Cne x x)) = _
      rw [cmp32_ne_self])
  have hc2 : eval_expr A E.ge empty_env le m (.Ebinop .Ole (tmp h .f32) minusOne32 tint)
      (Val.of_bool (IEEE32.le x m1Bits32)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd eval_minusOne32 (by
      show some (Val.of_bool (LClight.Float32.cmp .Cle x m1Bits32)) = _
      rw [cmp32_le])
  have hc3 : eval_expr A E.ge empty_env le m (.Ebinop .Oge (tmp h .f32) two64f tint)
      (Val.of_bool (IEEE32.le t64Bits32 x)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd (.eval_Econst_single _ _) (by
      show some (Val.of_bool (LClight.Float32.cmp .Cge x t64Bits32)) = _
      rw [cmp32_ge])
  unfold truncSat32UStmt
  cases hn : IEEE32.isNaN x
  · obtain ⟨h1, h2, h3⟩ := truncSat32U_cases x hn
    refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc1
      (by rw [hn]; exact bool_of_bool m false) ?_
    cases hl : IEEE32.le x m1Bits32
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc2
        (by rw [hl]; exact bool_of_bool m false) ?_
      cases hg : IEEE32.le t64Bits32 x
      · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc3
          (by rw [hg]; exact bool_of_bool m false) ?_
        refine .exec_Sset _ _ _ _ _ _ (.eval_Ecast _ _ _ _ hd ?_)
        show (match LClight.Float32.to_longu x with
          | some i => some (val.Vlong i)
          | none => none) = _
        rw [h3 hl hg]
      · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc3
          (by rw [hg]; exact bool_of_bool m true) ?_
        rw [h2 hl hg]
        exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc2
        (by rw [hl]; exact bool_of_bool m true) ?_
      rw [h1 hl]
      exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)
  · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc1
      (by rw [hn]; exact bool_of_bool m true) ?_
    have : IEEE32.truncSatI64U x = 0 := by simp [IEEE32.truncSatI64U, hn]
    rw [this]
    exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_long _ _)

/-- `truncSat32SStmt h` sets the `i32` slot at height `h` to Talos's `i32.trunc_sat_f32_s` of
the float. -/
theorem exec_truncSat32S {le : temp_env} {m : mem} {h : Nat} {x : UInt32}
    (hx : le[slotId h .f32]? = some (.Vsingle x)) :
    exec_stmt A X E.ge empty_env le m (truncSat32SStmt h) E0
      (le.insert (slotId h .i32) (.Vint (IEEE32.truncSatI32S x))) m .Out_normal := by
  have hd : eval_expr A E.ge empty_env le m (tmp h .f32) (.Vsingle x) := .eval_Etempvar _ _ _ hx
  have hc1 : eval_expr A E.ge empty_env le m (.Ebinop .One (tmp h .f32) (tmp h .f32) tint)
      (Val.of_bool (IEEE32.isNaN x)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd hd (by
      show some (Val.of_bool (LClight.Float32.cmp .Cne x x)) = _
      rw [cmp32_ne_self])
  have hc2 : eval_expr A E.ge empty_env le m (.Ebinop .Ole (tmp h .f32) minusTwo31f tint)
      (Val.of_bool (IEEE32.le x m31Bits32)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd eval_minusTwo31f (by
      show some (Val.of_bool (LClight.Float32.cmp .Cle x m31Bits32)) = _
      rw [cmp32_le])
  have hc3 : eval_expr A E.ge empty_env le m (.Ebinop .Oge (tmp h .f32) two31f tint)
      (Val.of_bool (IEEE32.le t31Bits32 x)) :=
    .eval_Ebinop _ _ _ _ _ _ _ hd (.eval_Econst_single _ _) (by
      show some (Val.of_bool (LClight.Float32.cmp .Cge x t31Bits32)) = _
      rw [cmp32_ge])
  unfold truncSat32SStmt
  cases hn : IEEE32.isNaN x
  · obtain ⟨h1, h2, h3⟩ := truncSat32S_cases x hn
    refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc1
      (by rw [hn]; exact bool_of_bool m false) ?_
    cases hl : IEEE32.le x m31Bits32
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc2
        (by rw [hl]; exact bool_of_bool m false) ?_
      cases hg : IEEE32.le t31Bits32 x
      · refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc3
          (by rw [hg]; exact bool_of_bool m false) ?_
        refine .exec_Sset _ _ _ _ _ _ (.eval_Ecast _ _ (.Vint (IEEE32.truncSatI32S x)) _
          (.eval_Ecast _ _ _ _ hd ?_) (cast_int_uint m _))
        show (match LClight.Float32.to_int x with
          | some i => some (val.Vint (cast_int_int .I32 .Signed i))
          | none => none) = _
        rw [h3 hl hg]
        rfl
      · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc3
          (by rw [hg]; exact bool_of_bool m true) ?_
        rw [h2 hl hg]
        exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_int _ _)
    · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc2
        (by rw [hl]; exact bool_of_bool m true) ?_
      rw [h1 hl]
      exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_int _ _)
  · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc1
      (by rw [hn]; exact bool_of_bool m true) ?_
    have : IEEE32.truncSatI32S x = 0 := by simp [IEEE32.truncSatI32S, hn]
    rw [this]
    exact .exec_Sset _ _ _ _ _ _ (.eval_Econst_int _ _)

theorem sim_i64TruncSatF32U (F : Nat) : InstrSim A X E mod c F .i64TruncSatF32U := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_exec hrest hinv.locals hinv.brk hb (exec_truncSat32U hx) (te_insert_same _ _ _)
        rfl (fun id hid _ => te_insert_ne _ (Ne.symm hid)) hinv.store hinv.status

theorem sim_i32TruncSatF32S (F : Nat) : InstrSim A X E mod c F .i32TruncSatF32S := by
  intro L σ n s σ' n' h hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨hb, rfl, rfl, rfl, rfl⟩ := h
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f' =>
      obtain ⟨x, vr, hvs, hx, hrest⟩ := pop1_f32 hinv.stack
      simp only [execOne.eq_def, hvs]
      exact push_exec hrest hinv.locals hinv.brk hb (exec_truncSat32S hx) (te_insert_same _ _ _)
        rfl (fun id hid _ => te_insert_ne _ (Ne.symm hid)) hinv.store hinv.status

end

end LeanExe.Native
