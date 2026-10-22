import Library.Numerics.Float64.Bessel.BesselOrderLoops
import Library.Numerics.Float64.Bessel.BesselDivTop
import LeanExe.ProofKit.F64TopMul
import LeanExe.ProofKit.F64TopPack
import LeanExe.ProofKit.F64Saturate
import LeanExe.ProofKit.F64PackingFinite
import LeanExe.ProofKit.F64NegateOps
import LeanExe.ProofKit.F64TwoSum

/-!
One step `(t ⊘ x) ⊗ b ⊖ a` of `yn`'s forward loop at every magnitude, for the loop below 2, where
the values can reach the overflow threshold.  The rounding of a magnitude yields either a finite
word of the requested sign (`F64Packing.pack_finite_spec`) or the infinity of that sign
(`pack_infinite`), so a product or sum of finite words that is not finite is an infinity of the
sign of the exact result (`mul_nonfinite`, `add_nonfinite`).  A product of magnitude at least
`2^1024 - 2^970` rounds to an infinity (`mul_overflow`), as does a sum (`add_overflow_abs`).  With
`q` within `u L + 2^-1075` of `L ≥ 1`: a finite result lies within
`u (3.01 L |b| + |a|) + 2^-1070` of `L b - a` (`step_fin`); the result is finite when `L |b|` and
`|L b - a|` are at most `2^1024 - 2^1019` (`step_mag`); and a result that is not finite is negative
infinity when `b < 0` (`step_inf`).  `loop_stop` evaluates `yn`'s loop when the values are finite
up to an index where the value is negative infinity, which stops the loop.  `div_pos_big` states
that a positive quotient of at least twice a positive word `v` rounds to positive infinity or to a
finite word of value at least that of `v`.
-/

namespace Library.Numerics.Float64.Bessel.BesselYnSteps
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselStepF BesselOrderLoops
  F64NearestNonnegative

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 4096

theorem signMask_finite (s : Bool) : Finite (Wasm.IEEE64.signMask s) := by
  cases s <;> unfold CodeLib.IEEE64.Finite <;> decide

theorem signMask_sign (s : Bool) : Wasm.IEEE64.sign (Wasm.IEEE64.signMask s) = s := by
  cases s <;> decide

theorem neg_inf_bits : Wasm.IEEE64.infinity true = 0xFFF0000000000000 := by decide

/-- A rounded magnitude that is not finite is the infinity of the requested sign. -/
theorem pack_infinite (neg : Bool) (n : ℕ)
    (hf : ¬Finite (Wasm.IEEE64.roundScaledMagnitude neg n)) :
    Wasm.IEEE64.roundScaledMagnitude neg n = Wasm.IEEE64.infinity neg := by
  by_cases h1 : n < 2 ^ 52
  · exfalso
    apply hf
    have h1' : n < 4503599627370496 := h1
    have e : Wasm.IEEE64.roundScaledMagnitude neg n = Wasm.IEEE64.encodeFinite neg 0 n := by
      simp [Wasm.IEEE64.roundScaledMagnitude, h1']
    rw [e]
    exact finite_encodeFinite neg 0 n (by norm_num) h1
  by_cases h2 : n < 2 ^ 53
  · exfalso
    apply hf
    have h1' : ¬n < 4503599627370496 := h1
    have h2' : n < 9007199254740992 := h2
    have e : Wasm.IEEE64.roundScaledMagnitude neg n =
        Wasm.IEEE64.encodeFinite neg 1 (n - 2 ^ 52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, h1', h2']
    rw [e]
    exact finite_encodeFinite neg 1 _ (by norm_num) (by omega)
  have hn : 2 ^ 53 ≤ n := by omega
  have hsub : ¬n < 4503599627370496 := by omega
  have hexact : ¬n < 9007199254740992 := by omega
  let shift := Nat.log2 n - 52
  let rounded := Wasm.IEEE32.roundShift n shift
  obtain ⟨hshift, hlo, hhi⟩ := F64Packing.significand_bounds n hn
  change 0 < shift at hshift
  change 2 ^ 52 ≤ rounded at hlo
  change rounded ≤ 2 ^ 53 at hhi
  by_cases hc : rounded = 2 ^ 53
  · have hcn : Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = 9007199254740992 := hc
    have heq : Wasm.IEEE64.roundScaledMagnitude neg n =
        if 2047 ≤ shift + 2 then Wasm.IEEE64.infinity neg
        else Wasm.IEEE64.encodeFinite neg (shift + 2) 0 := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsub, hexact, hcn, shift, Nat.add_assoc]
    by_cases he : 2047 ≤ shift + 2
    · rw [heq, ite_eq_left he]
    · exfalso
      apply hf
      rw [heq, ite_eq_right he]
      exact finite_encodeFinite neg _ 0 (by omega) (by norm_num)
  · have hcn : ¬Wasm.IEEE32.roundShift n (Nat.log2 n - 52) = 9007199254740992 := hc
    have heq : Wasm.IEEE64.roundScaledMagnitude neg n =
        if 2047 ≤ shift + 1 then Wasm.IEEE64.infinity neg
        else Wasm.IEEE64.encodeFinite neg (shift + 1) (rounded - 2 ^ 52) := by
      simp [Wasm.IEEE64.roundScaledMagnitude, hsub, hexact, hcn, shift, rounded]
    by_cases he : 2047 ≤ shift + 1
    · rw [heq, ite_eq_left he]
    · exfalso
      apply hf
      rw [heq, ite_eq_right he]
      exact finite_encodeFinite neg _ _ (by omega) (by omega)

/-- A product of finite words is a signed zero or a rounded magnitude, with the sign of the exact
product. -/
theorem mul_cases (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.signMask (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) ∨
      ∃ m, Wasm.IEEE64.mul a b =
        Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) m := by
  simp only [Wasm.IEEE64.mul, not_nan_of_finite ha, not_nan_of_finite hb,
    not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
    ite_false]
  split
  · left; rfl
  · unfold Wasm.IEEE64.roundDyadicMagnitude
    split
    · left; rfl
    · right; exact ⟨_, rfl⟩

theorem mul_nonfinite (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : ¬Finite (Wasm.IEEE64.mul a b)) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.infinity (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  rcases mul_cases a b ha hb with h | ⟨m, h⟩
  · rw [h] at hf
    exact absurd (signMask_finite _) hf
  · rw [h] at hf ⊢
    exact pack_infinite _ _ hf

theorem mul_sign (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : Finite (Wasm.IEEE64.mul a b)) :
    Wasm.IEEE64.sign (Wasm.IEEE64.mul a b) = (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  rcases mul_cases a b ha hb with h | ⟨m, h⟩
  · rw [h, signMask_sign]
  · rw [h] at hf ⊢
    exact (F64Packing.pack_finite_spec _ m hf).2

theorem add_nonfinite (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : ¬Finite (Wasm.IEEE64.add a b)) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.infinity
      (decide (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b < 0)) := by
  revert hf
  simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
    not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
    ite_false]
  split
  · intro hf
    exfalso
    apply hf
    split
    · exact signMask_finite true
    · unfold CodeLib.IEEE64.Finite; decide
  · exact pack_infinite _ _

/-- A product of magnitude at least `2^1024 - 2^970` is not finite. -/
theorem mul_overflow (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h : 2 ^ 1024 - 2 ^ 970 ≤ |value a * value b|) : ¬Finite (Wasm.IEEE64.mul a b) := by
  obtain ⟨n, hn⟩ : ∃ n, n = Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b :=
    ⟨_, rfl⟩
  have hv : |value a * value b| = (n : ℝ) / 2 ^ 2148 := by
    rw [abs_mul, F64RoundNearest.abs_value, F64RoundNearest.abs_value, hn]
    push_cast
    ring
  have hnlo : 2 ^ 3172 - 2 ^ 3118 ≤ n := by
    rw [hv, le_div_iff₀ (by positivity)] at h
    have e : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 2148 = 2 ^ 3172 - 2 ^ 3118 := by norm_num
    have e' : ((2 ^ 3172 - 2 ^ 3118 : ℕ) : ℝ) = 2 ^ 3172 - 2 ^ 3118 := by norm_num
    have : ((2 ^ 3172 - 2 ^ 3118 : ℕ) : ℝ) ≤ n := by rw [e']; linarith
    exact_mod_cast this
  have hbig : (2 : ℕ) ^ 3171 < 2 ^ 3172 - 2 ^ 3118 := by norm_num
  have hn0 : n ≠ 0 := by omega
  have ha0 : (Wasm.IEEE64.scaledMagnitude a == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h0
    rw [h0, zero_mul] at hn
    exact hn0 hn
  have hb0 : (Wasm.IEEE64.scaledMagnitude b == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h0
    rw [h0, mul_zero] at hn
    exact hn0 hn
  have hmul : Wasm.IEEE64.mul a b = Wasm.IEEE64.roundDyadicMagnitude
      (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n 1074 := by
    simp only [Wasm.IEEE64.mul, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, ha0, hb0, Bool.or_false,
      Bool.false_eq_true, ite_false, hn]
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hL : 3171 ≤ Nat.log2 n := by
    by_contra hc
    push Not at hc
    have : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ 3171 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- the rounded significand times its scale is at least the overflow threshold
  have hcand : 2 ^ 2098 - 2 ^ 2044 ≤
      Wasm.IEEE32.roundShift n (1074 + (Nat.log2 n - (1074 + 52))) *
        2 ^ (Nat.log2 n - (1074 + 52)) := by
    by_cases hL' : Nat.log2 n = 3171
    · rw [hL', show (3171 : ℕ) - (1074 + 52) = 2045 by norm_num,
        show (1074 : ℕ) + 2045 = 3119 by norm_num]
      have hlt : n < 2 ^ 3172 := by rw [hL'] at hL2; exact hL2
      have hq : n / 2 ^ 3119 = 2 ^ 53 - 1 := by
        apply Nat.div_eq_of_lt_le
        · have : (2 ^ 53 - 1) * 2 ^ 3119 = 2 ^ 3172 - 2 ^ 3119 := by norm_num
          have h2 : (2 : ℕ) ^ 3172 - 2 ^ 3119 ≤ 2 ^ 3172 - 2 ^ 3118 := by norm_num
          omega
        · have : (2 ^ 53 - 1 + 1) * 2 ^ 3119 = 2 ^ 3172 := by norm_num
          omega
      have hrem : 2 ^ 3119 / 2 ≤ n % 2 ^ 3119 := by
        have h1 := Nat.div_add_mod n (2 ^ 3119)
        rw [hq] at h1
        have h3 : (2 : ℕ) ^ 3119 / 2 = 2 ^ 3118 := by norm_num
        have h4 : 2 ^ 3119 * (2 ^ 53 - 1) = 2 ^ 3172 - 2 ^ 3119 := by norm_num
        have h5 : (2 : ℕ) ^ 3172 - 2 ^ 3118 = 2 ^ 3172 - 2 ^ 3119 + 2 ^ 3118 := by norm_num
        omega
      rw [F64Saturate.roundShift_up n 3119 (2 ^ 53 - 1) hq (by norm_num) hrem]
      norm_num
    · have hL3 : 3172 ≤ Nat.log2 n := by omega
      have hb := (CodeLib.IEEE32.roundShift_bounds n (1074 + (Nat.log2 n - (1074 + 52)))).1
      have hs : 1074 + (Nat.log2 n - (1074 + 52)) = Nat.log2 n - 52 := by omega
      rw [hs] at hb ⊢
      have hq : 2 ^ 52 ≤ n / 2 ^ (Nat.log2 n - 52) := by
        rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add,
          show 52 + (Nat.log2 n - 52) = Nat.log2 n by omega]
        exact hL1
      have hp : 2 ^ 2046 ≤ 2 ^ (Nat.log2 n - (1074 + 52)) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 ^ 2098 - 2 ^ 2044 ≤ 2 ^ 52 * 2 ^ 2046 := by norm_num
        _ ≤ Wasm.IEEE32.roundShift n (Nat.log2 n - 52) * 2 ^ (Nat.log2 n - (1074 + 52)) :=
          Nat.mul_le_mul (hq.trans hb) hp
  have hne : (n == 0) = false := by simpa using hn0
  have hsh : (Nat.log2 n - (1074 + 52) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega
  rw [hmul]
  unfold Wasm.IEEE64.roundDyadicMagnitude
  simp only [hne, hsh, Bool.false_eq_true, ite_false]
  rw [F64Saturate.round_overflow _ _ hcand]
  exact F64Packing.infinity_not_finite _

/-- A sum of magnitude at least `2^1024 - 2^970` is not finite. -/
theorem add_overflow_abs (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h : 2 ^ 1024 - 2 ^ 970 ≤ |value a + value b|) : ¬Finite (Wasm.IEEE64.add a b) := by
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := ⟨_, rfl⟩
  have hSv : value a + value b = (S : ℝ) / 2 ^ 1074 := by
    rw [value, value, hS]; push_cast; ring
  have hSlo : (2 : ℝ) ^ 2098 - 2 ^ 2044 ≤ |(S : ℝ)| := by
    rw [hSv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      le_div_iff₀ (by positivity)] at h
    linarith [(by norm_num : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 1074 = 2 ^ 2098 - 2 ^ 2044)]
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, abs_zero] at hSlo
    norm_num at hSlo
  have hb0 : (S == 0) = false := by simpa using hS0
  have hadd : Wasm.IEEE64.add a b =
      Wasm.IEEE64.roundScaledMagnitude (decide (S < 0)) S.natAbs := by
    simp only [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, Bool.or_false, Bool.false_eq_true,
      ite_false, ← hS, hb0]
  rw [hadd, F64Saturate.round_overflow]
  · exact F64Packing.infinity_not_finite _
  · have h1 : ((S.natAbs : ℕ) : ℝ) = |(S : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h2 : ((2 ^ 2098 - 2 ^ 2044 : ℕ) : ℝ) = 2 ^ 2098 - 2 ^ 2044 := by norm_num
    have : ((2 ^ 2098 - 2 ^ 2044 : ℕ) : ℝ) ≤ ((S.natAbs : ℕ) : ℝ) := by rw [h1, h2]; exact hSlo
    exact_mod_cast this

theorem sub_overflow (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (h : 2 ^ 1024 - 2 ^ 970 ≤ |value a - value b|) : ¬Finite (Wasm.IEEE64.sub a b) := by
  obtain ⟨hn, hv⟩ := F64Magnitude.negate_value b hb
  show ¬Finite (Wasm.IEEE64.add a (Wasm.IEEE64.negate b))
  apply add_overflow_abs a _ ha hn
  rw [hv, ← sub_eq_add_neg]
  exact h

theorem sub_inf (neg : Bool) (b : UInt64) (hb : Finite b) :
    Wasm.IEEE64.sub (Wasm.IEEE64.infinity neg) b = Wasm.IEEE64.infinity neg := by
  obtain ⟨hnf, -⟩ := F64Magnitude.negate_value b hb
  have h1 : Wasm.IEEE64.isNaN (Wasm.IEEE64.infinity neg) = false := by cases neg <;> decide
  have h2 : Wasm.IEEE64.isInfinite (Wasm.IEEE64.infinity neg) = true := by cases neg <;> decide
  simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, h1, h2, not_nan_of_finite hnf,
    not_infinite_of_finite hnf, Bool.or_false, Bool.false_and, Bool.false_eq_true, ite_false,
    ite_true]

theorem mul_inf_left (s : Bool) (b : UInt64) (hb : Finite b)
    (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0) :
    Wasm.IEEE64.mul (Wasm.IEEE64.infinity s) b =
      Wasm.IEEE64.infinity (s != Wasm.IEEE64.sign b) := by
  have h1 : Wasm.IEEE64.isNaN (Wasm.IEEE64.infinity s) = false := by cases s <;> decide
  have h2 : Wasm.IEEE64.isInfinite (Wasm.IEEE64.infinity s) = true := by cases s <;> decide
  have h3 : Wasm.IEEE64.sign (Wasm.IEEE64.infinity s) = s := by cases s <;> decide
  have hb0' : (Wasm.IEEE64.scaledMagnitude b == 0) = false := by simpa using hb0
  simp only [Wasm.IEEE64.mul, h1, h2, h3, not_nan_of_finite hb, hb0', Bool.or_false,
    Bool.false_eq_true, ite_false, ite_true]

theorem mul_inf_right (a : UInt64) (ha : Finite a) (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0)
    (s : Bool) :
    Wasm.IEEE64.mul a (Wasm.IEEE64.infinity s) =
      Wasm.IEEE64.infinity (Wasm.IEEE64.sign a != s) := by
  have h1 : Wasm.IEEE64.isNaN (Wasm.IEEE64.infinity s) = false := by cases s <;> decide
  have h2 : Wasm.IEEE64.isInfinite (Wasm.IEEE64.infinity s) = true := by cases s <;> decide
  have h3 : Wasm.IEEE64.sign (Wasm.IEEE64.infinity s) = s := by cases s <;> decide
  have ha0' : (Wasm.IEEE64.scaledMagnitude a == 0) = false := by simpa using ha0
  simp only [Wasm.IEEE64.mul, h1, h2, h3, not_nan_of_finite ha, not_infinite_of_finite ha, ha0',
    Bool.or_false, Bool.false_eq_true, ite_false, ite_true]

/-- A finite word has magnitude at most that of the largest finite double. -/
theorem abs_value_max (a : UInt64) (ha : Finite a) : |value a| ≤ 2 ^ 1024 - 2 ^ 971 := by
  have he : Wasm.IEEE64.exponent a < 2047 := by
    have h1 : Wasm.IEEE64.exponent a < 2048 := Nat.mod_lt _ (by norm_num)
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at ha
    simp only [bne_iff_ne, ne_eq] at ha
    omega
  have hf : Wasm.IEEE64.fraction a < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hm : Wasm.IEEE64.scaledMagnitude a ≤ (2 ^ 53 - 1) * 2 ^ 2045 := by
    unfold Wasm.IEEE64.scaledMagnitude
    dsimp only
    split
    · have : (2 : ℕ) ^ 52 ≤ (2 ^ 53 - 1) * 2 ^ 2045 := by norm_num
      omega
    · have hp : 2 ^ (Wasm.IEEE64.exponent a - 1) ≤ 2 ^ 2045 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact Nat.mul_le_mul (by omega) hp
  rw [F64RoundNearest.abs_value, div_le_iff₀ (by positivity)]
  have h1 : ((Wasm.IEEE64.scaledMagnitude a : ℕ) : ℝ) ≤ (((2 ^ 53 - 1) * 2 ^ 2045 : ℕ) : ℝ) := by
    exact_mod_cast hm
  have e : (((2 ^ 53 - 1) * 2 ^ 2045 : ℕ) : ℝ) = (2 ^ 1024 - 2 ^ 971) * 2 ^ 1074 := by norm_num
  linarith

/-- The rounding of one step at every magnitude, with `q` within `u L + 2^-1075` of `L ≥ 1`. -/
theorem step_arith_top {r p P vq vb va L : ℝ} (hL1 : 1 ≤ L)
    (hq : |vq - L| ≤ L / 2 ^ 53 + 1 / 2 ^ 1075) (hP : P = vq * vb)
    (hp : |p - P| ≤ 1 / 2 ^ 53 * |P| + 1 / 2 ^ 1075)
    (hr : |r - (p - va)| ≤ 1 / 2 ^ 53 * |p - va|) :
    |r - (L * vb - va)| ≤ 1 / 2 ^ 53 * (301 / 100 * L * |vb| + |va|) + 1 / 2 ^ 1070 := by
  have hV := abs_nonneg vb
  have hL0 : 0 ≤ L := by linarith
  have hX : 0 ≤ L * |vb| := mul_nonneg hL0 hV
  have hd : |vq - L| ≤ L * (1 / 2 ^ 53 + 1 / 2 ^ 1075) := by
    have : (1 : ℝ) / 2 ^ 1075 ≤ L * (1 / 2 ^ 1075) := le_mul_of_one_le_left (by positivity) hL1
    linarith
  have hq' : |vq| ≤ L * (1 + 1 / 2 ^ 53 + 1 / 2 ^ 1075) := by
    have := abs_sub_abs_le_abs_sub vq L
    rw [abs_of_nonneg hL0] at this
    linarith
  have hPb : |P| ≤ L * |vb| * (1 + 1 / 2 ^ 53 + 1 / 2 ^ 1075) := by
    rw [hP, abs_mul]
    calc |vq| * |vb| ≤ L * (1 + 1 / 2 ^ 53 + 1 / 2 ^ 1075) * |vb| :=
          mul_le_mul_of_nonneg_right hq' hV
      _ = L * |vb| * (1 + 1 / 2 ^ 53 + 1 / 2 ^ 1075) := by ring
  have hpa : |p - va| ≤ |P| * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + |va| := by
    have h1 := abs_sub va p
    have h2 : |p| ≤ |P| + |p - P| := by
      have := abs_add_le (p - P) P
      rw [sub_add_cancel] at this
      linarith
    have h3 := abs_sub p va
    linarith
  have e : r - (L * vb - va) = (r - (p - va)) + (p - P) + (vq - L) * vb := by rw [hP]; ring
  have h4 : |(vq - L) * vb| ≤ L * (1 / 2 ^ 53 + 1 / 2 ^ 1075) * |vb| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hd hV
  have h5 : |r - (L * vb - va)| ≤ |r - (p - va)| + |p - P| + |(vq - L) * vb| := by
    rw [e]
    have := abs_add_le (r - (p - va) + (p - P)) ((vq - L) * vb)
    have := abs_add_le (r - (p - va)) (p - P)
    linarith
  have hc : (1 + 1 / 2 ^ 53 + 1 / 2 ^ 1075) * (1 / 2 ^ 53 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 53) +
      (1 / 2 ^ 53 + 1 / 2 ^ 1075) ≤ (301 / 100 : ℝ) * (1 / 2 ^ 53) := by norm_num
  have h6 : |P| * (1 / 2 ^ 53 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 53) ≤
      L * |vb| * (1 + 1 / 2 ^ 53 + 1 / 2 ^ 1075) *
        (1 / 2 ^ 53 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 53) :=
    mul_le_mul_of_nonneg_right hPb (by positivity)
  have h7 := mul_le_mul_of_nonneg_left hc hX
  have e2 : L * (1 / 2 ^ 53 + 1 / 2 ^ 1075) * |vb| = L * |vb| * (1 / 2 ^ 53 + 1 / 2 ^ 1075) := by
    ring
  linarith

/-- A finite step lies within `u (3.01 L |b| + |a|) + 2^-1070` of `L b - a`. -/
theorem step_fin {q b a : UInt64} {L : ℝ} (hq : Finite q)
    (hqL : |value q - L| ≤ L / 2 ^ 53 + 1 / 2 ^ 1075) (hL1 : 1 ≤ L) (hb : Finite b)
    (ha : Finite a) (hr : Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul q b) a)) :
    |value (Wasm.IEEE64.sub (Wasm.IEEE64.mul q b) a) - (L * value b - value a)| ≤
      𝐮 * (301 / 100 * L * |value b| + |value a|) + 1 / 2 ^ 1070 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have heps : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  have hp : Finite (Wasm.IEEE64.mul q b) := by
    by_contra hpn
    rw [mul_nonfinite q b hq hb hpn, sub_inf _ a ha] at hr
    exact F64Packing.infinity_not_finite _ hr
  have hqb : |value q * value b| < 2 ^ 1024 - 2 ^ 970 := by
    by_contra h
    push Not at h
    exact mul_overflow q b hq hb h hp
  obtain ⟨-, hpe⟩ := F64TopMul.mul_real_top q b hq hb hqb
  have hpa : |value (Wasm.IEEE64.mul q b) - value a| < 2 ^ 1024 - 2 ^ 970 := by
    by_contra h
    push Not at h
    exact sub_overflow _ a hp ha h hr
  obtain ⟨-, hre⟩ := F64TopPack.sub_real_relative_top _ a hp ha hpa
  rw [heps, hu] at hpe
  rw [hu] at hre ⊢
  exact step_arith_top hL1 hqL rfl hpe hre

/-- A step with `L |b|` and `|L b - a|` at most `2^1024 - 2^1019` is finite. -/
theorem step_mag {q b a : UInt64} {L : ℝ} (hq : Finite q)
    (hqL : |value q - L| ≤ L / 2 ^ 53 + 1 / 2 ^ 1075) (hL1 : 1 ≤ L) (hb : Finite b)
    (ha : Finite a) (h1 : L * |value b| ≤ 2 ^ 1024 - 2 ^ 1019)
    (h2 : |L * value b - value a| ≤ 2 ^ 1024 - 2 ^ 1019) :
    Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul q b) a) := by
  have heps : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hV := abs_nonneg (value b)
  have hL0 : 0 ≤ L := by linarith
  have hd : |value q - L| ≤ L * (1 / 2 ^ 52) := by
    have : (1 : ℝ) / 2 ^ 1075 ≤ L * (1 / 2 ^ 1075) := le_mul_of_one_le_left (by positivity) hL1
    have : L / 2 ^ 53 + L * (1 / 2 ^ 1075) ≤ L * (1 / 2 ^ 52) := by
      have : (1 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 52 := by norm_num
      linarith
    linarith
  have hdb : |value q * value b - L * value b| ≤ L * |value b| * (1 / 2 ^ 52) := by
    rw [← sub_mul, abs_mul]
    calc |value q - L| * |value b| ≤ L * (1 / 2 ^ 52) * |value b| :=
          mul_le_mul_of_nonneg_right hd hV
      _ = L * |value b| * (1 / 2 ^ 52) := by ring
  have hLb : |L * value b| = L * |value b| := by rw [abs_mul, abs_of_nonneg hL0]
  have hqb1 : |value q * value b| ≤ (2 ^ 1024 - 2 ^ 1019) * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub (value q * value b) (L * value b)
    rw [hLb] at this
    linarith
  have hqb : |value q * value b| < 2 ^ 1024 - 2 ^ 970 := by
    have : ((2 : ℝ) ^ 1024 - 2 ^ 1019) * (1 + 1 / 2 ^ 52) < 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  obtain ⟨hpf, hpe⟩ := F64TopMul.mul_real_top q b hq hb hqb
  rw [heps, hu] at hpe
  have hpa : |value (Wasm.IEEE64.mul q b) - value a| < 2 ^ 1024 - 2 ^ 970 := by
    have e : value (Wasm.IEEE64.mul q b) - value a = (L * value b - value a) +
        (value q * value b - L * value b) + (value (Wasm.IEEE64.mul q b) - value q * value b) := by
      ring
    rw [e]
    have t1 := abs_add_le ((L * value b - value a) + (value q * value b - L * value b))
      (value (Wasm.IEEE64.mul q b) - value q * value b)
    have t2 := abs_add_le (L * value b - value a) (value q * value b - L * value b)
    have t3 : L * |value b| * (1 / 2 ^ 52) ≤ (2 ^ 1024 - 2 ^ 1019) * (1 / 2 ^ 52) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have t4 : 1 / 2 ^ 53 * |value q * value b| ≤
        1 / 2 ^ 53 * ((2 ^ 1024 - 2 ^ 1019) * (1 + 1 / 2 ^ 52)) :=
      mul_le_mul_of_nonneg_left hqb1 (by positivity)
    have : ((2 : ℝ) ^ 1024 - 2 ^ 1019) + (2 ^ 1024 - 2 ^ 1019) * (1 / 2 ^ 52) +
        (1 / 2 ^ 53 * ((2 ^ 1024 - 2 ^ 1019) * (1 + 1 / 2 ^ 52)) + 1 / 2 ^ 1075) <
        2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  exact (F64TopPack.sub_real_relative_top _ a hpf ha hpa).1

/-- A step that is not finite, with `q > 0` and `b < 0`, is negative infinity. -/
theorem step_inf {q b a : UInt64} (hq : Finite q) (hq0 : 0 < value q) (hb : Finite b)
    (hb0 : value b < 0) (ha : Finite a)
    (hr : ¬Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul q b) a)) :
    Wasm.IEEE64.sub (Wasm.IEEE64.mul q b) a = Wasm.IEEE64.infinity true := by
  have hsq : Wasm.IEEE64.sign q = false := F64Exact.sign_of_pos q hq0
  have hsb : Wasm.IEEE64.sign b = true := by
    by_contra h
    have := F64TwoSum.value_nonneg_of_sign b (by simpa using h)
    linarith
  have hneg : (Wasm.IEEE64.sign q != Wasm.IEEE64.sign b) = true := by rw [hsq, hsb]; rfl
  by_cases hp : Finite (Wasm.IEEE64.mul q b)
  · have hps := mul_sign q b hq hb hp
    rw [hneg] at hps
    have hp0 := F64TwoSum.value_nonpos_of_sign _ hps
    obtain ⟨hna, hva⟩ := F64Magnitude.negate_value a ha
    change ¬Finite (Wasm.IEEE64.add (Wasm.IEEE64.mul q b) (Wasm.IEEE64.negate a)) at hr
    show Wasm.IEEE64.add (Wasm.IEEE64.mul q b) (Wasm.IEEE64.negate a) = _
    rw [add_nonfinite _ _ hp hna hr]
    congr 1
    rw [decide_eq_true_iff]
    by_contra hS
    push Not at hS
    have hsum : 0 ≤ value (Wasm.IEEE64.mul q b) + value (Wasm.IEEE64.negate a) := by
      rw [value, value, ← add_div]
      apply div_nonneg _ (by positivity)
      exact_mod_cast hS
    have hbig : 2 ^ 1024 - 2 ^ 970 ≤
        |value (Wasm.IEEE64.mul q b) + value (Wasm.IEEE64.negate a)| := by
      by_contra h
      push Not at h
      exact hr (F64TopPack.add_real_relative_top _ _ hp hna h).1
    have hmax := abs_value_max (Wasm.IEEE64.negate a) hna
    rw [abs_of_nonneg hsum] at hbig
    have := le_abs_self (value (Wasm.IEEE64.negate a))
    have : (2 : ℝ) ^ 1024 - 2 ^ 971 < 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  · rw [mul_nonfinite q b hq hb hp, hneg]
    exact sub_inf true a ha

/-- A positive quotient of at least twice a nonnegative word `v` rounds to positive infinity or to
a positive finite word of value at least that of `v`. -/
theorem div_pos_big (a b v : UInt64) (ha : Finite a) (hb : Finite b)
    (hsa : Wasm.IEEE64.sign a = false) (hsb : Wasm.IEEE64.sign b = false)
    (hv : v.toNat < 0x7FF0000000000000) (hv0 : 0 ≤ value v)
    (hlo : 1 / 2 ^ 1022 ≤ value a / value b) (hs : 2 * value v ≤ value a / value b) :
    Wasm.IEEE64.div a b = Wasm.IEEE64.infinity false ∨
      (Finite (Wasm.IEEE64.div a b) ∧ Wasm.IEEE64.sign (Wasm.IEEE64.div a b) = false ∧
        value v ≤ value (Wasm.IEEE64.div a b)) := by
  have hnear : ∀ c, Nearest (value a / value b) c →
      Finite c ∧ Wasm.IEEE64.sign c = false ∧ value v ≤ value c := by
    intro c hc
    have hcl : c.toNat < 0x7FF0000000000000 := hc.1
    refine ⟨?_, ?_, ?_⟩
    · unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
      simp only [bne_iff_ne, ne_eq, Nat.reducePow]
      omega
    · simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le, Nat.reducePow]
      omega
    · have h := hc.2 v hv
      have hvs : value v ≤ value a / value b :=
        le_trans (le_add_of_nonneg_left hv0) (by linarith : value v + value v ≤ value a / value b)
      rw [abs_of_nonpos (sub_nonpos.mpr hvs)] at h
      have := neg_abs_le (value c - value a / value b)
      linarith
  by_cases h22 : value a / value b < 2 ^ 1022
  · right
    exact hnear _ (F64NearestDiv.div_nearest a b ha hb hsa hsb hlo h22)
  · push Not at h22
    rcases BesselDivTop.div_top a b ha hb hsa hsb h22 with ⟨h1, -⟩ | ⟨h1, -⟩
    · left
      rw [h1]
      decide
    · right
      exact hnear _ h1

/-- `yn`'s loop stops at the first index `K` whose value is negative infinity. -/
theorem loop_stop (x a0 a1 : Float) (n : UInt64) (K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31) (hfin : ∀ j, 1 ≤ j → j < K → Finite (ya x a0 a1 j).toBits)
    (hinf : (ya x a0 a1 K).toBits = 0xFFF0000000000000) :
    (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), a0, a1) (ycond n) (ystep x)).2.2 =
      ya x a0 a1 K := by
  unfold LeanExe.repeatWhile
  rw [go_iterate (ycond n) (ystep x) (K - 1) _ _ (by simp only [UInt64.reduceToNat]; omega)]
  · rw [ystep_iter, show K - 1 + 1 = K by omega]
  · intro j hj
    rw [ystep_iter]
    simp only [ycond, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, high_ne_of_finite _ (hfin (j + 1) (by omega) (by omega))⟩
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  · rw [ystep_iter, show K - 1 + 1 = K by omega]
    show (decide (UInt64.ofNat K < n) && ((ya x a0 a1 K).toBits >>> 32 != 0xFFF00000)) = false
    rw [hinf, Bool.and_eq_false_iff]
    right
    decide

#print axioms pack_infinite
#print axioms mul_overflow
#print axioms step_fin
#print axioms step_mag
#print axioms step_inf
#print axioms div_pos_big
#print axioms loop_stop

end Library.Numerics.Float64.Bessel.BesselYnSteps
