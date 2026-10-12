import LeanExe.ProofKit.F64Exact

/-!
Results of the binary64 operations at their saturation points, proved from the definitions in
`Wasm.IEEE64` without evaluating them.  A magnitude of at least `2 ^ 1024 - 2 ^ 970`, the midpoint
between the largest finite double and `2 ^ 1024`, rounds to infinity (`round_overflow`), and a
dyadic magnitude below half the smallest subnormal rounds to zero (`round_dyadic_zero`).  The
remaining lemmas state the results of a division by zero, of `0/0`, of `∞/∞`, and of an operation
with a NaN operand.
-/

namespace LeanExe.ProofKit.F64Saturate
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- Rounding `n` at `2 ^ s` rounds up when the remainder is at least half and the quotient is
odd. -/
theorem roundShift_up (n s q : ℕ) (hq : n / 2 ^ s = q) (hodd : q % 2 = 1)
    (hrem : 2 ^ s / 2 ≤ n % 2 ^ s) : Wasm.IEEE32.roundShift n s = q + 1 := by
  unfold Wasm.IEEE32.roundShift
  simp only [hq]
  rw [ite_eq_right (not_lt.mpr hrem)]
  by_cases h : 2 ^ s / 2 < n % 2 ^ s
  · rw [ite_eq_left h]
  · have hq2 : (q % 2 == 0) = false := by simp [hodd]
    rw [ite_eq_right h, hq2]
    rfl

/-- A magnitude of at least `2 ^ 1024 - 2 ^ 970` in scaled units rounds to infinity. -/
theorem round_overflow (neg : Bool) (n : ℕ) (hn : 2 ^ 2098 - 2 ^ 2044 ≤ n) :
    Wasm.IEEE64.roundScaledMagnitude neg n = Wasm.IEEE64.infinity neg := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    have : (2 : ℕ) ^ 2044 < 2 ^ 2098 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    omega
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hL : 2097 ≤ Nat.log2 n := by
    by_contra h
    push Not at h
    have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ 2097 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ 2097 < 2 ^ 2098 - 2 ^ 2044 := by norm_num
    omega
  have hbig1 : ¬ n < 2 ^ 52 := by
    have : (2 : ℕ) ^ 52 ≤ 2 ^ 2098 - 2 ^ 2044 := by norm_num
    omega
  have hbig2 : ¬ n < 2 ^ 53 := by
    have : (2 : ℕ) ^ 53 ≤ 2 ^ 2098 - 2 ^ 2044 := by norm_num
    omega
  unfold Wasm.IEEE64.roundScaledMagnitude
  rw [ite_eq_right hbig1, ite_eq_right hbig2]
  by_cases hL' : Nat.log2 n = 2097
  · -- `n` lies in the top binade; the rounded significand is `2 ^ 53`
    have hlt : n < 2 ^ 2098 := by rw [hL'] at hL2; exact hL2
    have hsh : Nat.log2 n - 52 = 2045 := by omega
    have hq : n / 2 ^ 2045 = 2 ^ 53 - 1 := by
      apply Nat.div_eq_of_lt_le
      · have : (2 ^ 53 - 1) * 2 ^ 2045 = 2 ^ 2098 - 2 ^ 2045 := by norm_num
        have h2 : (2 : ℕ) ^ 2098 - 2 ^ 2045 ≤ 2 ^ 2098 - 2 ^ 2044 := by norm_num
        omega
      · have : (2 ^ 53 - 1 + 1) * 2 ^ 2045 = 2 ^ 2098 := by norm_num
        omega
    have hrem : 2 ^ 2045 / 2 ≤ n % 2 ^ 2045 := by
      have h1 := Nat.div_add_mod n (2 ^ 2045)
      rw [hq] at h1
      have h3 : (2 : ℕ) ^ 2045 / 2 = 2 ^ 2044 := by norm_num
      have h4 : 2 ^ 2045 * (2 ^ 53 - 1) = 2 ^ 2098 - 2 ^ 2045 := by norm_num
      have h5 : (2 : ℕ) ^ 2098 - 2 ^ 2044 = 2 ^ 2098 - 2 ^ 2045 + 2 ^ 2044 := by norm_num
      omega
    have hr : Wasm.IEEE32.roundShift n 2045 = 2 ^ 53 := by
      rw [roundShift_up n 2045 (2 ^ 53 - 1) hq (by norm_num) hrem]
      norm_num
    simp only [hsh, hr, beq_self_eq_true, ite_true]
    rw [ite_eq_left (by norm_num)]
  · have hsh : 2046 ≤ Nat.log2 n - 52 := by omega
    by_cases hr : Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = 2 ^ 53
    · simp only [hr, beq_self_eq_true, ite_true]
      rw [ite_eq_left (by omega)]
    · have : (Wasm.IEEE32.roundShift n (Nat.log2 n - 52) == 2 ^ 53) = false := by simpa using hr
      simp only [this, Bool.false_eq_true, ite_false]
      rw [ite_eq_left (by omega)]

/-- A positive dyadic magnitude below `2 ^ 1073` units of `2 ^ -2148` rounds to a zero. -/
theorem round_dyadic_zero (neg : Bool) (n : ℕ) (h0 : 0 < n) (hn : n < 2 ^ 1073) :
    Wasm.IEEE64.roundDyadicMagnitude neg n 1074 = Wasm.IEEE64.encodeFinite neg 0 0 := by
  have hlog : Nat.log2 n < 1073 := (Nat.log2_lt (by omega)).mpr hn
  have hsh : Nat.log2 n - (1074 + 52) = 0 := by omega
  have hne : (n == 0) = false := by simpa using h0.ne'
  have hr : Wasm.IEEE32.roundShift n 1074 = 0 := by
    unfold Wasm.IEEE32.roundShift
    have hq : n / 2 ^ 1074 = 0 := Nat.div_eq_of_lt (hn.trans (by norm_num))
    have hm : n % 2 ^ 1074 = n := Nat.mod_eq_of_lt (hn.trans (by norm_num))
    have hh : (2 : ℕ) ^ 1074 / 2 = 2 ^ 1073 := by norm_num
    simp only [hq, hm, hh, hn, ite_true]
  unfold Wasm.IEEE64.roundDyadicMagnitude
  simp only [hne, hsh, beq_self_eq_true, Bool.false_eq_true, ite_false, ite_true,
    show ((1074 : ℕ) == 0) = false from rfl, hr]
  unfold Wasm.IEEE64.roundScaledMagnitude
  rw [ite_eq_left (by norm_num)]

/-- A finite nonzero word divided by a zero is the infinity of the sign of the quotient. -/
theorem div_by_zero (w z : UInt64) (hw : Finite w) (hz : Finite z)
    (hw0 : Wasm.IEEE64.scaledMagnitude w ≠ 0) (hz0 : Wasm.IEEE64.scaledMagnitude z = 0) :
    Wasm.IEEE64.div w z =
      Wasm.IEEE64.infinity (Wasm.IEEE64.sign w != Wasm.IEEE64.sign z) := by
  have hwz : (Wasm.IEEE64.scaledMagnitude w == 0) = false := by simpa using hw0
  simp only [Wasm.IEEE64.div, not_nan_of_finite hw, not_nan_of_finite hz,
    not_infinite_of_finite hw, not_infinite_of_finite hz, hz0, hwz, Bool.or_false,
    Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]

/-- Zero divided by zero is the canonical NaN. -/
theorem div_zero_zero (w z : UInt64) (hw : Finite w) (hz : Finite z)
    (hw0 : Wasm.IEEE64.scaledMagnitude w = 0) (hz0 : Wasm.IEEE64.scaledMagnitude z = 0) :
    Wasm.IEEE64.div w z = Wasm.IEEE64.canonicalNaN := by
  simp only [Wasm.IEEE64.div, not_nan_of_finite hw, not_nan_of_finite hz,
    not_infinite_of_finite hw, not_infinite_of_finite hz, hz0, hw0, Bool.or_false,
    Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]

/-- An infinity divided by an infinity is the canonical NaN. -/
theorem div_inf_inf (w z : UInt64) (hwn : Wasm.IEEE64.isNaN w = false)
    (hzn : Wasm.IEEE64.isNaN z = false) (hw : Wasm.IEEE64.isInfinite w = true)
    (hz : Wasm.IEEE64.isInfinite z = true) :
    Wasm.IEEE64.div w z = Wasm.IEEE64.canonicalNaN := by
  simp only [Wasm.IEEE64.div, hwn, hzn, hw, hz, Bool.or_false, Bool.false_eq_true, ite_false,
    ite_true]

/-- A sum with a NaN operand is the canonical NaN. -/
theorem add_nan_left (w z : UInt64) (hw : Wasm.IEEE64.isNaN w = true) :
    Wasm.IEEE64.add w z = Wasm.IEEE64.canonicalNaN := by
  simp only [Wasm.IEEE64.add, hw, Bool.true_or, ite_true]

#print axioms round_overflow
#print axioms round_dyadic_zero
#print axioms div_by_zero
#print axioms div_zero_zero
#print axioms div_inf_inf
#print axioms add_nan_left

end LeanExe.ProofKit.F64Saturate
