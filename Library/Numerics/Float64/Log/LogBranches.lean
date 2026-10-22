import Library.Numerics.Float64.Log.Compiled
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64Sign

/-!
The paths of `Log.logWith` by the bits of the argument, and the exact results outside the
logarithm's open domain and at 1: `log (±0)` is negative infinity, `log (+∞)` is positive
infinity, a negative argument or a NaN gives the canonical NaN, and `log 1` is positive zero.
The guards compare 64-bit words, so each lemma states its condition on `x.toBits.toNat`.
-/

namespace Library.Numerics.Float64.Log.LogBranches
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem near_guard (ix : UInt64) :
    ix - 4606619468846596096 < 4607473789381378048 - 4606619468846596096 ↔
      4606619468846596096 ≤ ix.toNat ∧ ix.toNat < 4607473789381378048 := by
  have hix := ix.toNat_lt
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_sub]
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

theorem top_guard (ix : UInt64) :
    ix >>> 48 - 16 ≥ 32752 - 16 ↔
      ix.toNat < 4503599627370496 ∨ 9218868437227405312 ≤ ix.toNat := by
  have hix := ix.toNat_lt
  rw [ge_iff_le, UInt64.le_iff_toNat_le, UInt64.toNat_sub, UInt64.toNat_sub,
    UInt64.toNat_shiftRight]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem double_guard (ix : UInt64) : (ix * 2 == 0) = true ↔ ix.toNat % 9223372036854775808 = 0 := by
  have hix := ix.toNat_lt
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mul]
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

theorem word_guard (ix c : UInt64) : (ix == c) = true ↔ ix.toNat = c.toNat := by
  rw [beq_iff_eq, UInt64.toNat_inj]

/-- For a word below `2 ^ 52`, the bits that mark a negative number or a NaN are clear. -/
theorem small_top (ix : UInt64) (h : ix.toNat < 4503599627370496) :
    (ix >>> 48 &&& 32768 != 0 || ix >>> 48 &&& 32752 == 32752) = false := by
  have ht : (ix >>> 48).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  have key : ∀ n : Fin 16,
      (UInt64.ofNat n.val &&& 32768 != 0 || UInt64.ofNat n.val &&& 32752 == 32752) = false := by
    decide +kernel
  have h := key ⟨(ix >>> 48).toNat, ht⟩
  simpa only [UInt64.ofNat_toNat] using h

/-- For a word with the sign bit set, the sign bit of the top 16 bits is set. -/
theorem negative_top (ix : UInt64) (h : 9223372036854775808 ≤ ix.toNat) :
    (ix >>> 48 &&& 32768 != 0 || ix >>> 48 &&& 32752 == 32752) = true := by
  have hix := ix.toNat_lt
  have hb : ((ix >>> 48) &&& 32768).toNat ≠ 0 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    intro hz
    have ht : (ix.toNat / 2 ^ 48 &&& 32768).testBit 15 = true := by
      rw [show (32768 : Nat) = 2 ^ 15 by norm_num, Nat.testBit_and, Nat.testBit_two_pow_self,
        Bool.and_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
      simp only [Nat.reducePow]
      omega
    rw [hz] at ht
    simp at ht
  have hne : ((ix >>> 48) &&& 32768 != 0) = true := by
    rw [bne_iff_ne, ne_eq]
    intro heq
    apply hb
    rw [heq]
    rfl
  rw [hne, Bool.true_or]

/-- For a positive NaN pattern, the exponent bits of the top 16 bits are all set. -/
theorem nan_top (ix : UInt64) (h1 : 9218868437227405312 < ix.toNat)
    (h2 : ix.toNat < 9223372036854775808) :
    (ix >>> 48 &&& 32768 != 0 || ix >>> 48 &&& 32752 == 32752) = true := by
  have ht : 32752 ≤ (ix >>> 48).toNat ∧ (ix >>> 48).toNat < 32768 := by
    rw [UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  have key : ∀ n : Fin 16,
      (UInt64.ofNat (32752 + n.val) &&& 32768 != 0 ||
        UInt64.ofNat (32752 + n.val) &&& 32752 == 32752) = true := by
    decide +kernel
  have h := key ⟨(ix >>> 48).toNat - 32752, by omega⟩
  have he : 32752 + ((ix >>> 48).toNat - 32752) = (ix >>> 48).toNat := by omega
  simp only [he, UInt64.ofNat_toNat] at h
  exact h

theorem near_selected (tab tab2 : Array UInt64) (x : Float)
    (hlo : 4606619468846596096 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 4607473789381378048)
    (hne : x.toBits.toNat ≠ 4607182418800017408) :
    Log.logWith tab tab2 x = Log.logNear1 x := by
  have hg := (near_guard x.toBits).mpr ⟨hlo, hhi⟩
  have h1 : ¬ (x.toBits == 4607182418800017408) = true := by
    rw [word_guard]
    exact hne
  simp only [Log.logWith]
  rw [ite_eq_left hg, ite_eq_right h1]

theorem one_selected (tab tab2 : Array UInt64) (x : Float)
    (h : x.toBits.toNat = 4607182418800017408) :
    Log.logWith tab tab2 x = 0.0 := by
  have hg := (near_guard x.toBits).mpr ⟨by omega, by omega⟩
  have h1 : (x.toBits == 4607182418800017408) = true := by
    rw [word_guard]
    exact h
  simp only [Log.logWith]
  rw [ite_eq_left hg, ite_eq_left h1]

/-- A positive normal argument outside the path near 1 takes the main path. -/
theorem normal_selected (tab tab2 : Array UInt64) (x : Float)
    (hlo : 4503599627370496 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 9218868437227405312)
    (hnear : x.toBits.toNat < 4606619468846596096 ∨ 4607473789381378048 ≤ x.toBits.toNat) :
    Log.logWith tab tab2 x = Log.logCore tab tab2 x.toBits := by
  have hg : ¬ x.toBits - 4606619468846596096 < 4607473789381378048 - 4606619468846596096 := by
    rw [near_guard]
    omega
  have ht : ¬ x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [top_guard]
    omega
  simp only [Log.logWith]
  rw [ite_eq_right hg, ite_eq_right ht]

/-- A positive subnormal argument is scaled by `2 ^ 52` and takes the main path. -/
theorem subnormal_selected (tab tab2 : Array UInt64) (x : Float)
    (hlo : 0 < x.toBits.toNat) (hhi : x.toBits.toNat < 4503599627370496) :
    Log.logWith tab tab2 x =
      Log.logCore tab tab2 ((x * Float.ofBits 4841369599423283200).toBits - (52 : UInt64) <<< 52) := by
  have hg : ¬ x.toBits - 4606619468846596096 < 4607473789381378048 - 4606619468846596096 := by
    rw [near_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [top_guard]
    omega
  have hd : ¬ (x.toBits * 2 == 0) = true := by
    rw [double_guard]
    omega
  have hi : ¬ (x.toBits == 9218868437227405312) = true := by
    rw [word_guard]
    simp only [UInt64.reduceToNat]
    omega
  have hs := small_top x.toBits hhi
  simp only [Log.logWith]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_right hd, ite_eq_right hi, hs, ite_eq_right Bool.false_ne_true]

theorem zero_selected (tab tab2 : Array UInt64) (x : Float)
    (h : x.toBits.toNat % 9223372036854775808 = 0) :
    Log.logWith tab tab2 x = -1.0 / 0.0 := by
  have hg : ¬ x.toBits - 4606619468846596096 < 4607473789381378048 - 4606619468846596096 := by
    rw [near_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [top_guard]
    omega
  have hd : (x.toBits * 2 == 0) = true := (double_guard _).mpr h
  simp only [Log.logWith]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_left hd]

theorem infinity_selected (tab tab2 : Array UInt64) (x : Float)
    (h : x.toBits.toNat = 9218868437227405312) :
    Log.logWith tab tab2 x = x := by
  have hg : ¬ x.toBits - 4606619468846596096 < 4607473789381378048 - 4606619468846596096 := by
    rw [near_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [top_guard]
    omega
  have hd : ¬ (x.toBits * 2 == 0) = true := by
    rw [double_guard]
    omega
  have hi : (x.toBits == 9218868437227405312) = true := by
    rw [word_guard]
    exact h
  simp only [Log.logWith]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_right hd, ite_eq_left hi]

/-- A negative argument other than `-0`, or a positive NaN pattern, takes the invalid path. -/
theorem invalid_selected (tab tab2 : Array UInt64) (x : Float)
    (h : (9223372036854775808 ≤ x.toBits.toNat ∧ x.toBits.toNat ≠ 9223372036854775808) ∨
      (9218868437227405312 < x.toBits.toNat ∧ x.toBits.toNat < 9223372036854775808)) :
    Log.logWith tab tab2 x = (x - x) / (x - x) := by
  have hix := x.toBits.toNat_lt
  have hg : ¬ x.toBits - 4606619468846596096 < 4607473789381378048 - 4606619468846596096 := by
    rw [near_guard]
    omega
  have ht : x.toBits >>> 48 - 16 ≥ 32752 - 16 := by
    rw [top_guard]
    omega
  have hd : ¬ (x.toBits * 2 == 0) = true := by
    rw [double_guard]
    omega
  have hi : ¬ (x.toBits == 9218868437227405312) = true := by
    rw [word_guard]
    simp only [UInt64.reduceToNat]
    omega
  have hs : (x.toBits >>> 48 &&& 32768 != 0 || x.toBits >>> 48 &&& 32752 == 32752) = true := by
    rcases h with h | h
    · exact negative_top _ h.1
    · exact nan_top _ h.1 h.2
  simp only [Log.logWith]
  rw [ite_eq_right hg, ite_eq_left ht, ite_eq_right hd, ite_eq_right hi, ite_eq_left hs]

/-- Subtracting a finite word from itself gives positive zero. -/
theorem sub_self_finite (a : UInt64) (ha : Finite a) : Wasm.IEEE64.sub a a = 0 := by
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value a ha
  have hs := (F64Sign.fields_negate a).2.2
  have hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate a) = 0 := by
    have h := negate_spec a ha
    rw [h.2]
    ring
  simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hnf,
    not_infinite_of_finite ha, not_infinite_of_finite hnf, Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, hsum, beq_self_eq_true, hs]
  cases Wasm.IEEE64.sign a <;> rfl

theorem invalid_bits (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true ∨ Finite x.toBits ∨
    x.toBits = 0xFFF0000000000000) :
    ((x - x) / (x - x)).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [F64Bits.toBits_div, F64Bits.toBits_sub]
  rcases h with h | h | h
  · have hc : Wasm.IEEE64.sub x.toBits x.toBits = Wasm.IEEE64.canonicalNaN := by
      simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, h, Bool.true_or, ↓reduceIte]
    rw [hc]
    decide +kernel
  · rw [sub_self_finite _ h]
    decide +kernel
  · rw [h]
    decide +kernel

#print axioms near_selected
#print axioms one_selected
#print axioms normal_selected
#print axioms subnormal_selected
#print axioms zero_selected
#print axioms infinity_selected
#print axioms invalid_selected
#print axioms invalid_bits

end Library.Numerics.Float64.Log.LogBranches
