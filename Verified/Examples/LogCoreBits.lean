import Verified.Examples.Log
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64Magnitude
import CodeLib.IEEE64.Conversions

/-!
The word arithmetic of `Log.logCore`.  The argument word `ix` stands for `(2 ^ 52 + f) 2 ^ (E - 1075)`
with `E · 2 ^ 52 + f` equal to `ix` modulo `2 ^ 64`, where `E` reaches down to `-51` for a
subnormal argument scaled by `2 ^ 52`.  With `tmp = ix - 0x3fe6000000000000`, the code takes the
subinterval `i` from bits 45 to 51 of `tmp`, `k` from the arithmetic shift of `tmp` by 52, and the
word of `z = x 2 ^ -k` by removing `k` from the exponent field.  `logCore_eq` restates
`Log.logCore` through `reduced`, the computation of `r`, and `finalOf`, the arithmetic after it.
-/

namespace Verified.Examples.LogCoreBits
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

def tmpOf (ix : UInt64) : UInt64 := ix - 0x3fe6000000000000
def indexOf (ix : UInt64) : UInt64 := (tmpOf ix >>> 45) % 128
def kOf (ix : UInt64) : UInt64 :=
  (tmpOf ix >>> 52) ||| (if tmpOf ix >>> 63 == 1 then 0xFFFFFFFFFFFFF000 else 0)
def zOf (ix : UInt64) : UInt64 := ix - (tmpOf ix &&& ((0xfff : UInt64) <<< 52))
def kdOf (k : UInt64) : Float := if k >>> 63 == 1 then -(0 - k).toFloat else k.toFloat

/-- `r ≈ z/c - 1` from `z` and the entries `chi`, `clo`, and `invc`. -/
def reduced (z chi clo invc : Float) : Float := (z - chi - clo) * invc

/-- The arithmetic of `Log.logCore` after `r`, `kd`, and `logc`. -/
def finalOf (r kd logc : Float) : Float :=
  let ln2hi := Float.ofBits 0x3FE62E42FEFA3800
  let ln2lo := Float.ofBits 0x3D2EF35793C76730
  let A0 := Float.ofBits 0xBFE0000000000001
  let A1 := Float.ofBits 0x3FD555555551305B
  let A2 := Float.ofBits 0xBFCFFFFFFFEB4590
  let A3 := Float.ofBits 0x3FC999B324F10111
  let A4 := Float.ofBits 0xBFC55575E506C89F
  let w := kd * ln2hi + logc
  let hi := w + r
  let lo := w - hi + r + kd * ln2lo
  let r2 := r * r
  lo + r2 * A0 + r * r2 * (A1 + r * A2 + r2 * (A3 + r * A4)) + hi

theorem logCore_eq (tab tab2 : Array UInt64) (ix : UInt64) :
    Log.logCore tab tab2 ix =
      finalOf (reduced (Float.ofBits (zOf ix)) (Float.ofBits tab2[(2 * indexOf ix).toNat]!)
          (Float.ofBits tab2[(2 * indexOf ix + 1).toNat]!) (Float.ofBits tab[(2 * indexOf ix).toNat]!))
        (kdOf (kOf ix)) (Float.ofBits tab[(2 * indexOf ix + 1).toNat]!) := rfl

theorem and_high (T : Nat) (hT : T < 2 ^ 64) :
    T &&& 18442240474082181120 = T / 2 ^ 52 * 2 ^ 52 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hm : (18442240474082181120 : Nat) = (2 ^ 12 - 1) * 2 ^ 52 := by norm_num
  rw [Nat.testBit_and, hm, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : 52 ≤ j
  · have he : j - 52 + 52 = j := by omega
    rw [he]
    by_cases hj2 : j < 64
    · simp [hj, show j - 52 < 12 by omega]
    · have h1 : T.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1]
  · simp [hj]

theorem or_high (Q : Nat) (hQ : Q < 2 ^ 12) :
    Q ||| 18446744073709547520 = 18446744073709547520 + Q := by
  rw [Nat.or_comm, show (18446744073709547520 : Nat) = 2 ^ 12 * (2 ^ 52 - 1) by norm_num,
    ← Nat.two_pow_add_eq_or_of_lt hQ]

/-- The words of `tmp`, `i`, `k`, and `z` in terms of `ix`. -/
theorem fields (ix : UInt64) :
    (indexOf ix).toNat = (tmpOf ix).toNat / 35184372088832 % 128 ∧
    (zOf ix).toNat = (18446744073709551616 - (tmpOf ix).toNat / 4503599627370496 * 4503599627370496 +
      ix.toNat) % 18446744073709551616 ∧
    (tmpOf ix).toNat = (18446744073709551616 - 4604367669032910848 + ix.toNat) %
      18446744073709551616 ∧
    (kOf ix).toNat = (if (tmpOf ix).toNat / 9223372036854775808 = 1 then
      18446744073709547520 + (tmpOf ix).toNat / 4503599627370496
      else (tmpOf ix).toNat / 4503599627370496) := by
  have hT := (tmpOf ix).toNat_lt
  have hA : (tmpOf ix &&& (4095 : UInt64) <<< 52).toNat =
      (tmpOf ix).toNat / 4503599627370496 * 4503599627370496 := by
    rw [UInt64.toNat_and, show ((4095 : UInt64) <<< 52).toNat = 18442240474082181120 by decide,
      and_high _ hT]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [indexOf, UInt64.toNat_mod, UInt64.toNat_shiftRight, UInt64.reduceToNat,
      Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  · simp only [zOf, UInt64.toNat_sub, hA, Nat.reducePow]
  · simp only [tmpOf, UInt64.toNat_sub, UInt64.reduceToNat, Nat.reducePow]
  · have hQ : (tmpOf ix >>> 52).toNat = (tmpOf ix).toNat / 4503599627370496 := by
      simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]
    have hS : (tmpOf ix >>> 63).toNat = (tmpOf ix).toNat / 9223372036854775808 := by
      simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
        Nat.shiftRight_eq_div_pow, Nat.reducePow]
    have hQlt : (tmpOf ix).toNat / 4503599627370496 < 2 ^ 12 := by
      simp only [Nat.reducePow] at hT ⊢
      omega
    by_cases hc : (tmpOf ix).toNat / 9223372036854775808 = 1
    · have hb : (tmpOf ix >>> 63 == 1) = true := by
        rw [beq_iff_eq, ← UInt64.toNat_inj, hS, hc]
        rfl
      simp only [kOf, hb, ↓reduceIte, UInt64.toNat_or, hQ, hc, UInt64.reduceToNat]
      exact or_high _ hQlt
    · have hb : ¬ (tmpOf ix >>> 63 == 1) = true := by
        rw [beq_iff_eq, ← UInt64.toNat_inj, hS]
        exact hc
      simp only [kOf, hb, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_or, hQ, hc,
        UInt64.reduceToNat, Nat.or_zero]

/-- The fields for an argument whose fraction field is at least `0x6000000000000`: `z` has
exponent field 1022, `i` is the top seven fraction bits less 48, and `k = E - 1022`. -/
theorem fields_upper (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496) (hf6 : 1688849860263936 ≤ f)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    (zOf ix).toNat = 1022 * 4503599627370496 + f ∧
    (indexOf ix).toNat = f / 35184372088832 - 48 ∧
    ((kOf ix).toNat : Int) = (E - 1022) % 18446744073709551616 := by
  obtain ⟨hi, hz, ht, hk⟩ := fields ix
  have hN := ix.toNat_lt
  simp only [Nat.reducePow] at hN
  refine ⟨?_, ?_, ?_⟩
  · rw [hz]; omega
  · rw [hi]; omega
  · rw [hk]; split_ifs <;> omega

/-- The fields for an argument whose fraction field is below `0x6000000000000`: `z` has exponent
field 1023, `i` is the top seven fraction bits plus 80, and `k = E - 1023`. -/
theorem fields_lower (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf6 : f < 1688849860263936)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    (zOf ix).toNat = 1023 * 4503599627370496 + f ∧
    (indexOf ix).toNat = f / 35184372088832 + 80 ∧
    ((kOf ix).toNat : Int) = (E - 1023) % 18446744073709551616 := by
  obtain ⟨hi, hz, ht, hk⟩ := fields ix
  have hN := ix.toNat_lt
  simp only [Nat.reducePow] at hN
  refine ⟨?_, ?_, ?_⟩
  · rw [hz]; omega
  · rw [hi]; omega
  · rw [hk]; split_ifs <;> omega

/-- A word holding an integer of magnitude at most `2 ^ 53` converts exactly. -/
theorem convert_exact (n : UInt64) (hn : n.toNat ≤ 2 ^ 53) :
    Finite (Wasm.IEEE64.convertI64U n) ∧ value (Wasm.IEEE64.convertI64U n) = (n.toNat : ℝ) := by
  have h := F64GridExact.signed_grid_packing_exact (n.toNat : Int) 1074 (by simpa using hn)
    (by norm_num)
  have hd : decide ((n.toNat : Int) < 0) = false := by simp
  have ha : (n.toNat : Int).natAbs = n.toNat := by simp
  rw [hd, ha] at h
  rw [CodeLib.IEEE64.convert_i64_unsigned_spec]
  refine ⟨h.1, ?_⟩
  have h2 : (2 : ℝ) ^ 1074 ≠ 0 := by positivity
  rw [value, h.2, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, mul_div_assoc,
    div_self h2, mul_one]

/-- `kd` is the integer `k` that the word `K` holds in two's complement. -/
theorem kd_value (K : UInt64) (k : Int) (hk1 : -262144 ≤ k) (hk2 : k ≤ 262144)
    (hK : (K.toNat : Int) = k % 18446744073709551616) :
    Finite (kdOf K).toBits ∧ value (kdOf K).toBits = (k : ℝ) := by
  have hKlt := K.toNat_lt
  simp only [Nat.reducePow] at hKlt
  rcases lt_or_ge k 0 with hneg | hpos
  · obtain ⟨m, hmk⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hmk
    have hc : (K >>> 63 == 1) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      omega
    have hm : (0 - K).toNat = m := by
      rw [UInt64.toNat_sub]
      simp only [UInt64.reduceToNat, Nat.reducePow]
      omega
    obtain ⟨hf, hv⟩ := convert_exact (0 - K) (by rw [hm]; simp only [Nat.reducePow]; omega)
    simp only [kdOf, hc, ↓reduceIte]
    rw [F64Bits.toBits_neg, F64Convert.toBits_toFloat]
    simp only [F64Sign.sub_negZero, not_nan_of_finite hf, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value _ hf
    refine ⟨hnf, ?_⟩
    rw [hnv, hv, hm, Int.cast_neg, Int.cast_natCast]
  · obtain ⟨m, hmk⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    subst hmk
    have hc : ¬ (K >>> 63 == 1) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      omega
    have hm : K.toNat = m := by omega
    obtain ⟨hf, hv⟩ := convert_exact K (by rw [hm]; simp only [Nat.reducePow]; omega)
    simp only [kdOf, hc, Bool.false_eq_true, ↓reduceIte]
    rw [F64Convert.toBits_toFloat]
    refine ⟨hf, ?_⟩
    rw [hv, hm, Int.cast_natCast]

#print axioms logCore_eq
#print axioms and_high
#print axioms or_high
#print axioms fields
#print axioms fields_upper
#print axioms fields_lower
#print axioms convert_exact
#print axioms kd_value

end Verified.Examples.LogCoreBits
