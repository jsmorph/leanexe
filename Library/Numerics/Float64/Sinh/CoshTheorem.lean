import Library.Numerics.Float64.Sinh.CoshSmall
import Library.Numerics.Float64.Sinh.CoshMid
import Library.Numerics.Float64.Sinh.SinhLdexp

/-!
`Sinh.cosh` within one step of `cosh x` on every finite input, and its exceptional results.  The
proof selects the branch of `Sinh.coshWith` from the high word of `abs(x)` and applies
`CoshSmall.cosh_tiny` below `2 ^ -55`, `CoshSmall.cosh_small` below `0.34657359`,
`CoshMid.cosh_mid` below 22, `CoshLarge.cosh_large` below `709.7822265625`, and
`SinhLdexp.ldexp_within` up to `710.47607421875`.  Above, the code returns `1.0e+300 · 1.0e+300`,
positive infinity, and `cosh x` lies above the overflow threshold.  Both infinities give positive
infinity and a NaN gives the canonical NaN.
-/

namespace Library.Numerics.Float64.Sinh.CoshTheorem
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tanh.Expm1Branches Library.Numerics.Float64.Tanh.Expm1Theorem

set_option exponentiation.threshold 4096

theorem overflow_bits :
    (Float.ofBits 0x7E37E43C8800759C * Float.ofBits 0x7E37E43C8800759C).toBits =
      0x7FF0000000000000 := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  decide +kernel

/-- `cosh x` against `exp abs(x) / 2`. -/
theorem cosh_half (X : ℝ) :
    |Real.cosh X - Real.exp |X| / 2| ≤ Real.exp (-|X|) / 2 := by
  rw [← Real.cosh_abs, Real.cosh_eq,
    show (Real.exp |X| + Real.exp (-|X|)) / 2 - Real.exp |X| / 2 = Real.exp (-|X|) / 2 by ring,
    abs_of_pos (by positivity)]

/-- From `710.47607421875` on, `cosh x` lies above the overflow threshold. -/
theorem cosh_overflow (X : ℝ) (h : 71047607421875 / 10 ^ 11 ≤ |X|) :
    F64PositiveRounding.overflowThreshold ≤ Real.cosh X := by
  have hl := Library.Numerics.Float64.Exp.ExpTight.log_two_bounds.2
  have e := Library.Numerics.Float64.Exp.ExpTightFloat.exp_two_pow 1025
  push_cast at e
  have h1 : Real.exp (1025 * Real.log 2) ≤ Real.exp |X| := Real.exp_le_exp.mpr (by linarith)
  rw [e] at h1
  have h3 : Real.exp |X| / 2 ≤ Real.cosh X := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have := Real.exp_pos (-|X|)
    linarith
  have hth : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
  rw [hth]
  have : (2 : ℝ) ^ 1024 - 2 ^ 970 ≤ 2 ^ 1025 / 2 := by norm_num
  linarith

/-- `Sinh.cosh` lies within one step of `cosh x` on every finite input. -/
theorem cosh_within_one (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits)) (Sinh.cosh x).toBits := by
  have h1 := high_finite x.toBits hxf
  have h1' : ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) := h1
  unfold Sinh.cosh Sinh.coshWith
  simp only []
  rw [ite_eq_right h1']
  by_cases hs : highWord x.toBits < 1071001155
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1071001155 from hs)]
    by_cases ht : highWord x.toBits < 1015021568
    · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1015021568 from ht)]
      exact CoshSmall.cosh_tiny x hxf (high_lt_real x.toBits 1015021568 (by norm_num)
        (1 / 2 ^ 55) (1 / 2 ^ 55) (by norm_num) (by decide +kernel)
        (UInt64.lt_iff_toNat_lt.mp ht))
    · rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 < 1015021568) from ht)]
      have htn : 1015021568 ≤ (highWord x.toBits).toNat := by
        have : ¬ (highWord x.toBits).toNat < 1015021568 :=
          fun h => ht (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      exact CoshSmall.cosh_small x hxf (high_ge_real x.toBits 1015021568 (by norm_num)
        (1 / 2 ^ 55) (1 / 2 ^ 55) (by norm_num) (by decide +kernel) htn)
        (high_lt x.toBits 1071001155 (by norm_num) (UInt64.lt_iff_toNat_lt.mp hs))
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 < 1071001155) from hs)]
  have hsn : 1071001155 ≤ (highWord x.toBits).toNat := by
    have : ¬ (highWord x.toBits).toNat < 1071001155 := fun h => hs (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hlo1 := high_ge_real x.toBits 1071001155 (by norm_num) (34657359 / 10 ^ 8)
    (34657359 / 10 ^ 8) (by norm_num) (by decide +kernel) hsn
  by_cases hm : highWord x.toBits < 1077280768
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1077280768 from hm)]
    exact CoshMid.cosh_mid x hxf hlo1 (high_lt_real x.toBits 1077280768 (by norm_num) 22 22
      (by norm_num) (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp hm))
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 < 1077280768) from hm)]
  have hmn : 1077280768 ≤ (highWord x.toBits).toNat := by
    have : ¬ (highWord x.toBits).toNat < 1077280768 := fun h => hm (UInt64.lt_iff_toNat_lt.mpr h)
    omega
  have hlo2 := high_ge_real x.toBits 1077280768 (by norm_num) 22 22 (by norm_num)
    (by decide +kernel) hmn
  by_cases hl : highWord x.toBits < 1082535490
  · rw [ite_eq_left (show x.toBits >>> 32 &&& 2147483647 < 1082535490 from hl)]
    have hhi := high_lt_real x.toBits 1082535490 (by norm_num) (7097822265625 / 10 ^ 10)
      (7097822265625 / 10 ^ 10) (by norm_num) (by decide +kernel)
      (UInt64.lt_iff_toNat_lt.mp hl)
    exact CoshLarge.cosh_large x hxf hlo2 (by linarith)
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
    exact (SinhLdexp.ldexp_within x hxf hlo3 hhi.le _ (cosh_half _)).1
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≤ 1082536910) from hd), overflow_bits]
  have hdn : 1082536911 ≤ (highWord x.toBits).toNat := by
    have : ¬ (highWord x.toBits).toNat ≤ 1082536910 := fun h => hd (UInt64.le_iff_toNat_le.mpr h)
    omega
  have hlo4 := high_ge_real x.toBits 1082536911 (by norm_num) (71047607421875 / 10 ^ 11)
    (71047607421875 / 10 ^ 11) (by norm_num) (by decide +kernel) hdn
  have hr := F64PositiveRounding.reference_overflow _ (cosh_overflow _ hlo4)
  exact F64SignedRounding.within_of_nonneg 1 _ (le_of_lt (Real.cosh_pos _)) _ (by decide)
    (by rw [hr]; unfold F64PositiveRounding.positiveInfinity; omega)
    (by rw [hr]; unfold F64PositiveRounding.positiveInfinity; omega)

theorem cosh_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Sinh.cosh x).toBits = 0x7FF0000000000000 := by
  have h1 : x.toBits >>> 32 &&& 2147483647 ≥ 2146435072 := by rw [h]; decide
  unfold Sinh.cosh Sinh.coshWith
  simp only []
  rw [ite_eq_left h1, F64Bits.toBits_mul, h]
  decide +kernel

theorem cosh_neg_infinity (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Sinh.cosh x).toBits = 0x7FF0000000000000 := by
  have h1 : x.toBits >>> 32 &&& 2147483647 ≥ 2146435072 := by rw [h]; decide
  unfold Sinh.cosh Sinh.coshWith
  simp only []
  rw [ite_eq_left h1, F64Bits.toBits_mul, h]
  decide +kernel

theorem cosh_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Sinh.cosh x).toBits = Wasm.IEEE64.canonicalNaN := by
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
  have h1' : x.toBits >>> 32 &&& 2147483647 ≥ 2146435072 := h1
  unfold Sinh.cosh Sinh.coshWith
  simp only []
  rw [ite_eq_left h1', F64Bits.toBits_mul]
  simp [Wasm.IEEE64.mul, h]

#print axioms cosh_within_one
#print axioms cosh_pos_infinity
#print axioms cosh_neg_infinity
#print axioms cosh_nan

end Library.Numerics.Float64.Sinh.CoshTheorem
