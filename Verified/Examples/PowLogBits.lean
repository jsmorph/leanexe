import Verified.Examples.Pow
import Verified.Examples.LogCoreBits

/-!
The word arithmetic of `Pow.powLog`.  As in `LogCoreBits`, the argument word `ix` stands for
`(2 ^ 52 + f) 2 ^ (E - 1075)` with `E · 2 ^ 52 + f` equal to `ix` modulo `2 ^ 64`, where `E`
reaches down to `-51` for a subnormal argument that `Pow.powWith` scales by `2 ^ 52`.  The offset
is `OFF = 0x3fe6955500000000`, whose fraction field is `0x6955500000000`: for a fraction field
from `0x6955500000000` on, `z` has exponent field 1022, `i` is `(f - 0x6955500000000) / 2 ^ 45`,
and `k = E - 1022`; below it, `z` has exponent field 1023, `i` is `(f + 2 ^ 52 -
0x6955500000000) / 2 ^ 45`, and `k = E - 1023`.  `powLog_eq` restates `Pow.powLog` through
`finalOf`, the arithmetic after the table lookup.
-/

namespace Verified.Examples.PowLogBits
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

def tmpOf (ix : UInt64) : UInt64 := ix - 0x3fe6955500000000
def indexOf (ix : UInt64) : UInt64 := (tmpOf ix >>> 45) % 128
def kOf (ix : UInt64) : UInt64 :=
  (tmpOf ix >>> 52) ||| (if tmpOf ix >>> 63 == 1 then 0xFFFFFFFFFFFFF000 else 0)
def zOf (ix : UInt64) : UInt64 := ix - (tmpOf ix &&& ((0xfff : UInt64) <<< 52))

/-- The word of `zhi`: the word `iz` of `z` rounded to a multiple of `2 ^ 32`. -/
def zhiOf (iz : UInt64) : UInt64 := (iz + ((1 : UInt64) <<< 31)) &&& 0xFFFFFFFF00000000

/-- The arithmetic of `Pow.powLog` after the table lookup, for the word `iz` of `z`. -/
def finalOf (iz : UInt64) (kd invc logc logctail : Float) : Float × Float :=
  let ln2hi := Float.ofBits 0x3FE62E42FEFA3800
  let ln2lo := Float.ofBits 0x3D2EF35793C76730
  let A0 := Float.ofBits 0xBFE0000000000000
  let A1 := Float.ofBits 0xBFE5555555555560
  let A2 := Float.ofBits 0x3FE0000000000006
  let A3 := Float.ofBits 0x3FE999999959554E
  let A4 := Float.ofBits 0xBFE555555529A47A
  let A5 := Float.ofBits 0xBFF2495B9B4845E9
  let A6 := Float.ofBits 0x3FF0002B8B263FC3
  let z := Float.ofBits iz
  let zhi := Float.ofBits (zhiOf iz)
  let zlo := z - zhi
  let rhi := zhi * invc - 1.0
  let rlo := zlo * invc
  let r := rhi + rlo
  let t1 := kd * ln2hi + logc
  let t2 := t1 + r
  let lo1 := kd * ln2lo + logctail
  let lo2 := t1 - t2 + r
  let ar := A0 * r
  let ar2 := r * ar
  let ar3 := r * ar2
  let arhi := A0 * rhi
  let arhi2 := rhi * arhi
  let hi := t2 + arhi2
  let lo3 := rlo * (ar + arhi)
  let lo4 := t2 - hi + arhi2
  let p := ar3 * (A1 + r * A2 + ar2 * (A3 + r * A4 + ar2 * (A5 + r * A6)))
  let lo := lo1 + lo2 + lo3 + lo4 + p
  let y := hi + lo
  (y, hi - y + lo)

theorem powLog_eq (tab : Array UInt64) (ix : UInt64) :
    Pow.powLog tab ix =
      finalOf (zOf ix) (LogCoreBits.kdOf (kOf ix)) (Float.ofBits tab[(4 * indexOf ix).toNat]!)
        (Float.ofBits tab[(4 * indexOf ix + 2).toNat]!)
        (Float.ofBits tab[(4 * indexOf ix + 3).toNat]!) := rfl

/-- The words of `tmp`, `i`, `k`, and `z` in terms of `ix`. -/
theorem fields (ix : UInt64) :
    (indexOf ix).toNat = (tmpOf ix).toNat / 35184372088832 % 128 ∧
    (zOf ix).toNat = (18446744073709551616 - (tmpOf ix).toNat / 4503599627370496 * 4503599627370496 +
      ix.toNat) % 18446744073709551616 ∧
    (tmpOf ix).toNat = (18446744073709551616 - 4604531861337669632 + ix.toNat) %
      18446744073709551616 ∧
    (kOf ix).toNat = (if (tmpOf ix).toNat / 9223372036854775808 = 1 then
      18446744073709547520 + (tmpOf ix).toNat / 4503599627370496
      else (tmpOf ix).toNat / 4503599627370496) := by
  have hT := (tmpOf ix).toNat_lt
  have hA : (tmpOf ix &&& (4095 : UInt64) <<< 52).toNat =
      (tmpOf ix).toNat / 4503599627370496 * 4503599627370496 := by
    rw [UInt64.toNat_and, show ((4095 : UInt64) <<< 52).toNat = 18442240474082181120 by decide,
      LogCoreBits.and_high _ hT]
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
      exact LogCoreBits.or_high _ hQlt
    · have hb : ¬ (tmpOf ix >>> 63 == 1) = true := by
        rw [beq_iff_eq, ← UInt64.toNat_inj, hS]
        exact hc
      simp only [kOf, hb, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_or, hQ, hc,
        UInt64.reduceToNat, Nat.or_zero]

/-- The fields for a fraction field from `0x6955500000000` on: `z` has exponent field 1022,
`i = (f - 0x6955500000000) / 2 ^ 45`, and `k = E - 1022`. -/
theorem fields_upper (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496) (hf6 : 1853042165022720 ≤ f)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    (zOf ix).toNat = 1022 * 4503599627370496 + f ∧
    (indexOf ix).toNat = (f - 1853042165022720) / 35184372088832 ∧
    ((kOf ix).toNat : Int) = (E - 1022) % 18446744073709551616 := by
  obtain ⟨hi, hz, ht, hk⟩ := fields ix
  have hN := ix.toNat_lt
  simp only [Nat.reducePow] at hN
  refine ⟨?_, ?_, ?_⟩
  · rw [hz]; omega
  · rw [hi]; omega
  · rw [hk]; split_ifs <;> omega

/-- The fields for a fraction field below `0x6955500000000`: `z` has exponent field 1023,
`i = (f + 2 ^ 52 - 0x6955500000000) / 2 ^ 45`, and `k = E - 1023`. -/
theorem fields_lower (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf6 : f < 1853042165022720)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    (zOf ix).toNat = 1023 * 4503599627370496 + f ∧
    (indexOf ix).toNat = (f + 2650557462347776) / 35184372088832 ∧
    ((kOf ix).toNat : Int) = (E - 1023) % 18446744073709551616 := by
  obtain ⟨hi, hz, ht, hk⟩ := fields ix
  have hN := ix.toNat_lt
  simp only [Nat.reducePow] at hN
  refine ⟨?_, ?_, ?_⟩
  · rw [hz]; omega
  · rw [hi]; omega
  · rw [hk]; split_ifs <;> omega

/-- The word of `zhi` for `iz = e 2 ^ 52 + f`: `iz` rounded to the nearest multiple of `2 ^ 32`,
halves up. -/
theorem zhi_toNat (iz : UInt64) (hiz : iz.toNat < 2 ^ 63) :
    (zhiOf iz).toNat = (iz.toNat + 2 ^ 31) / 2 ^ 32 * 2 ^ 32 := by
  have hadd : (iz + ((1 : UInt64) <<< 31)).toNat = iz.toNat + 2 ^ 31 := by
    rw [UInt64.toNat_add, show ((1 : UInt64) <<< 31).toNat = 2 ^ 31 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  rw [zhiOf, UInt64.toNat_and, hadd, show (0xFFFFFFFF00000000 : UInt64).toNat =
    (2 ^ 32 - 1) * 2 ^ 32 by decide]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : 32 ≤ j
  · have he : j - 32 + 32 = j := by omega
    rw [he]
    by_cases hj2 : j < 64
    · simp [hj, show j - 32 < 32 by omega]
    · have hlt : iz.toNat + 2 ^ 31 < 2 ^ j :=
        lt_of_lt_of_le (show iz.toNat + 2 ^ 31 < 2 ^ 64 by omega)
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h1 : (iz.toNat + 2 ^ 31).testBit j = false := Nat.testBit_lt_two_pow hlt
      rw [h1]
      simp
  · simp [hj]

#print axioms powLog_eq
#print axioms fields
#print axioms fields_upper
#print axioms fields_lower
#print axioms zhi_toNat

end Verified.Examples.PowLogBits
