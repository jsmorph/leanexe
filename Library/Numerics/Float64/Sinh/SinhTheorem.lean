import Library.Numerics.Float64.Sinh.SinhRanges

/-!
`Sinh.sinh` within three steps of `sinh x` on every finite input, and its exceptional results.
The proof selects the branch of `Sinh.sinhWith` from the high word of `abs(x)`, takes the factor
`h = ± 0.5` from the sign bit (`by_sign`), and applies the ranges: one step below `2 ^ -28` and
from 22 on, three steps between (`SinhSmallCases.sinh_small_pos`, `SinhMidCases.sinh_mid_pos`).
Both zeros return themselves, the infinities return themselves, and a NaN returns the canonical
NaN.
-/

namespace Library.Numerics.Float64.Sinh.SinhTheorem
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tanh.Expm1Branches Library.Numerics.Float64.Tanh.Expm1Theorem

set_option exponentiation.threshold 4096

/-- The sign bit of the high word. -/
theorem sign_shift (w : UInt64) : (w >>> 32 >>> 31 == 1) = Wasm.IEEE64.sign w := by
  rw [← sgn_iff]
  unfold sgn
  congr 1

/-- The factor `h` of `Sinh.sinhWith` from the sign of `x`. -/
theorem by_sign (x : Float) (hA : 0 < |value x.toBits|) (n : Nat) (g : Float → Float)
    (hpos : F64SignedRounding.WithinSteps n (Real.sinh |value x.toBits|) (g 0.5).toBits)
    (hneg : F64SignedRounding.WithinSteps n (-Real.sinh |value x.toBits|) (g (-0.5)).toBits) :
    F64SignedRounding.WithinSteps n (Real.sinh (value x.toBits))
      (g (if x.toBits >>> 32 >>> 31 == 1 then -0.5 else 0.5)).toBits := by
  rw [sign_shift]
  cases hs : Wasm.IEEE64.sign x.toBits
  · have hp := pos_of_sgn x.toBits (by rw [sgn_iff]; exact hs) hA
    rw [abs_of_pos hp] at hpos
    simpa using hpos
  · have hn := neg_of_sgn x.toBits (by rw [sgn_iff]; exact hs) hA
    rw [abs_of_neg hn, Real.sinh_neg, neg_neg] at hneg
    simpa using hneg

theorem shuge_add_gt (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 1) :
    Float.ofBits 0x7FAC7B1F3CAC7433 + x > 1.0 := by
  have hb : (Float.ofBits 0x7FAC7B1F3CAC7433).toBits = 0x7FAC7B1F3CAC7433 := by
    rw [F64Bits.toBits_ofBits]; decide +kernel
  have hhf : Finite (0x7FAC7B1F3CAC7433 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh := word_ge (10 ^ 306) (0x7FAC7B1F3CAC7433 : UInt64) (by decide +kernel)
  have hh1 := word_le (2 * 10 ^ 307) (0x7FAC7B1F3CAC7433 : UInt64) (by decide +kernel)
  push_cast at hh hh1
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  have h308 : (2 : ℝ) * 10 ^ 307 + 1 < 2 ^ 1023 := by norm_num
  have h306 : (0 : ℝ) < 10 ^ 306 - 1 := by norm_num
  have hs : |value 0x7FAC7B1F3CAC7433 + value x.toBits| < 2 ^ 1023 := by
    rw [abs_lt]; constructor <;> linarith
  have ha := F64AddBounds.add_real_relative _ _ hhf hxf hs
  rw [gt_iff_lt, F64Bits.lt_iff, F64Bits.toBits_add, hb, Library.Numerics.Float64.Tanh.TanhTheorem.one_bits,
    Library.Numerics.Float64.Tanh.Expm1FormsOne.lt_value _ _ Library.Numerics.Float64.Tanh.Expm1KernelInner.const_finite.1 ha.1, decide_eq_true_iff,
    Library.Numerics.Float64.Tanh.Expm1KernelInner.const_values.1]
  have hab := abs_le.mp ha.2
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hu] at hab
  have : (0 : ℝ) < value 0x7FAC7B1F3CAC7433 + value x.toBits := by linarith
  rw [abs_of_pos this] at hab
  nlinarith

/-- `Sinh.sinh` lies within three steps of `sinh x` on every finite input. -/
theorem sinh_within_three (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 3 (Real.sinh (value x.toBits)) (Sinh.sinh x).toBits := by
  have h1 := high_finite x.toBits hxf
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  unfold Sinh.sinh Sinh.sinhWith
  simp only []
  rw [ite_eq_right h1']
  by_cases h22 : highWord x.toBits < 1077280768
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1077280768 from h22)]
    have hhi22 := high_lt_real x.toBits 1077280768 (by norm_num) 22 22 (by norm_num)
      (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp h22)
    by_cases ht : highWord x.toBits < 1043333120
    · have hX := high_lt_real x.toBits 1043333120 (by norm_num) (1 / 2 ^ 28) (1 / 2 ^ 28)
        (by norm_num) (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp ht)
      have hsh := shuge_add_gt x hxf (hX.trans (by norm_num))
      have ht' : x.toBits >>> 32 &&& 2147483647 < 1043333120 := ht
      rw [ite_eq_left (by simp [ht', hsh])]
      exact Library.Numerics.Float64.Tanh.TanhTheorem.within_mono 1 3 (by norm_num) _ _ (SinhRanges.tiny_sinh _ hxf hX)
    have ht' : ¬ (x.toBits >>> 32 &&& 2147483647 < 1043333120) := ht
    rw [ite_eq_right (by simp [ht'])]
    have htn : 1043333120 ≤ (highWord x.toBits).toNat := by
      have : ¬ (highWord x.toBits).toNat < 1043333120 :=
        fun h => ht (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have hlo := high_ge_real x.toBits 1043333120 (by norm_num) (1 / 2 ^ 28) (1 / 2 ^ 28)
      (by norm_num) (by decide +kernel) htn
    have hA : 0 < |value x.toBits| := lt_of_lt_of_le (by norm_num) hlo
    by_cases h1x : highWord x.toBits < 1072693248
    · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1072693248 from h1x)]
      have hhi := high_lt_real x.toBits 1072693248 (by norm_num) 1 1 (by norm_num)
        (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp h1x)
      obtain ⟨hp, hn⟩ := SinhSmallCases.sinh_small_pos x hxf hlo hhi
      exact by_sign x hA 3 (fun h => h * (2.0 * Tanh.expm1 x.abs - Tanh.expm1 x.abs *
        Tanh.expm1 x.abs / (Tanh.expm1 x.abs + 1.0))) hp hn
    · rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 < 1072693248) from h1x)]
      have h1n : 1072693248 ≤ (highWord x.toBits).toNat := by
        have : ¬ (highWord x.toBits).toNat < 1072693248 :=
          fun h => h1x (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have hge := high_ge_real x.toBits 1072693248 (by norm_num) 1 1 (by norm_num)
        (by decide +kernel) h1n
      obtain ⟨hp, hn⟩ := SinhMidCases.sinh_mid_pos x hxf hge hhi22
      exact by_sign x hA 3 (fun h => h * (Tanh.expm1 x.abs + Tanh.expm1 x.abs /
        (Tanh.expm1 x.abs + 1.0))) hp hn
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 < 1077280768) from h22)]
  have h22n : 1077280768 ≤ (highWord x.toBits).toNat := by
    have : ¬ (highWord x.toBits).toNat < 1077280768 := fun h => h22 (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hlo2 := high_ge_real x.toBits 1077280768 (by norm_num) 22 22 (by norm_num)
    (by decide +kernel) h22n
  have hA : 0 < |value x.toBits| := lt_of_lt_of_le (by norm_num) hlo2
  by_cases hl : highWord x.toBits < 1082535490
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1082535490 from hl)]
    have hhi := high_lt_real x.toBits 1082535490 (by norm_num) (7097822265625 / 10 ^ 10)
      (7097822265625 / 10 ^ 10) (by norm_num) (by decide +kernel)
      (UInt64.lt_iff_toNat_lt.mp hl)
    obtain ⟨hp, hn⟩ := SinhRanges.sinh_large x hxf hlo2 (by linarith)
    exact Library.Numerics.Float64.Tanh.TanhTheorem.within_mono 1 3 (by norm_num) _ _
      (by_sign x hA 1 (fun h => h * Exp.exp x.abs) hp hn)
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 < 1082535490) from hl)]
  have hln : 1082535490 ≤ (highWord x.toBits).toNat := by
    have : ¬ (highWord x.toBits).toNat < 1082535490 := fun h => hl (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hlo3 := high_ge_real x.toBits 1082535490 (by norm_num) (7097822265625 / 10 ^ 10)
    (7097822265625 / 10 ^ 10) (by norm_num) (by decide +kernel) hln
  by_cases hd : highWord x.toBits ≤ 1082536910
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 ≤ 1082536910 from hd)]
    have hdn : (highWord x.toBits).toNat < 1082536911 := by
      have := UInt64.le_iff_toNat_le.mp hd
      change _ ≤ 1082536910 at this
      omega
    have hhi := high_lt_real x.toBits 1082536911 (by norm_num) (71047607421875 / 10 ^ 11)
      (71047607421875 / 10 ^ 11) (by norm_num) (by decide +kernel) hdn
    obtain ⟨hp, hn⟩ := SinhRanges.sinh_ldexp x hxf hlo3 hhi.le
    exact Library.Numerics.Float64.Tanh.TanhTheorem.within_mono 1 3 (by norm_num) _ _
      (by_sign x hA 1 (fun h => h * 2.0 * Sinh.ldexpExp Exp.expTable x.abs (0 - 1)) hp hn)
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≤ 1082536910) from hd)]
  have hdn : 1082536911 ≤ (highWord x.toBits).toNat := by
    have : ¬ (highWord x.toBits).toNat ≤ 1082536910 := fun h => hd (UInt64.le_iff_toNat_le.mpr h)
    omega
  have hlo4 := high_ge_real x.toBits 1082536911 (by norm_num) (71047607421875 / 10 ^ 11)
    (71047607421875 / 10 ^ 11) (by norm_num) (by decide +kernel) hdn
  exact Library.Numerics.Float64.Tanh.TanhTheorem.within_mono 1 3 (by norm_num) _ _ (SinhRanges.sinh_overflow x hxf hlo4)

theorem sinh_nonfinite (x : Float) (h : x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) :
    Sinh.sinh x = x + x := by
  unfold Sinh.sinh Sinh.sinhWith
  simp only []
  rw [ite_eq_left h]

theorem sinh_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Sinh.sinh x).toBits = 0x7FF0000000000000 := by
  rw [sinh_nonfinite x (by rw [h]; decide), F64Bits.toBits_add, h]
  decide +kernel

theorem sinh_neg_infinity (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Sinh.sinh x).toBits = 0xFFF0000000000000 := by
  rw [sinh_nonfinite x (by rw [h]; decide), F64Bits.toBits_add, h]
  decide +kernel

theorem sinh_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Sinh.sinh x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hn := h
  simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hn
  have h1 : highWord x.toBits ≥ 2146435072 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [highWord_toNat]
    change 2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32
    have : x.toBits.toNat % 2 ^ 63 / 2 ^ 52 = x.toBits.toNat / 2 ^ 52 % 2 ^ 11 := by
      rw [show (2 : Nat) ^ 63 = 2 ^ 52 * 2 ^ 11 by norm_num, Nat.mod_mul_right_div_self]
    omega
  rw [sinh_nonfinite x h1, F64Bits.toBits_add]
  simp [Wasm.IEEE64.add, h]

theorem sinh_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Sinh.sinh x).toBits = x.toBits := by
  have hhw : highWord x.toBits = 0 := by rcases h with h | h <;> rw [h] <;> decide
  have hxf : Finite x.toBits := by
    rcases h with h | h <;> rw [h] <;> unfold CodeLib.IEEE64.Finite <;> decide
  have hv : value x.toBits = 0 := by
    rcases h with h | h <;> rw [h]
    · exact F64Magnitude.value_zero
    · have : Wasm.IEEE64.scaledValue (0x8000000000000000 : UInt64) = 0 := by decide
      simp [value, this]
  have hsh := shuge_add_gt x hxf (by rw [hv]; norm_num)
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := by
    change ¬ highWord x.toBits ≥ 2146435072; rw [hhw]; decide
  have h22 : x.toBits >>> 32 &&& 2147483647 < 1077280768 := by
    change highWord x.toBits < 1077280768; rw [hhw]; decide
  have ht : x.toBits >>> 32 &&& 2147483647 < 1043333120 := by
    change highWord x.toBits < 1043333120; rw [hhw]; decide
  unfold Sinh.sinh Sinh.sinhWith
  simp only []
  rw [ite_eq_right h1', ite_eq_left h22, ite_eq_left (by simp [ht, hsh])]

#print axioms sinh_within_three
#print axioms sinh_pos_infinity
#print axioms sinh_neg_infinity
#print axioms sinh_nan
#print axioms sinh_zero

end Library.Numerics.Float64.Sinh.SinhTheorem
