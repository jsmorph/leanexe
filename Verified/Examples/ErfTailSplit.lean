import Verified.Examples.ErfMiddleBase
import LeanExe.ProofKit.F64ExactProduct
import LeanExe.ProofKit.F64NegateOps

/-!
The split of `x²` in `s_erf.c`'s tail.  `z` keeps the high 32 bits of `x`, so its significand has
21 bits: `scaledMagnitude z = m 2^(e + 31)` with `m < 2^21` for the exponent field `e` of `x`.
Hence `(-z) z` is exact (`F64ExactProduct.mul_exact_scaled`), `-z² - 0.5625` is exact on the grid
of `2^1034` scaled units, and `z - x` is exact on the grid of `x`'s unit (`F64ErrorTrack`'s exact
grid sums).  `z ≤ x < z + 2^-20 x`, so `(z - x)(z + x)` is small.
-/

namespace Verified.Examples.ErfTailSplit
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack

set_option exponentiation.threshold 4096

/-- Clearing the low 32 bits of a 64-bit number. -/
theorem land_mask (n : Nat) (hn : n < 2 ^ 64) :
    n &&& 18446744069414584320 = n / 2 ^ 32 * 2 ^ 32 := by
  have hM : (18446744069414584320 : Nat) = (2 ^ 32 - 1) * 2 ^ 32 := by norm_num
  rw [hM]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h1 : 32 ≤ i
  · by_cases h2 : i < 64
    · simp [h1, show i - 32 < 32 by omega, show i - 32 + 32 = i by omega]
    · have h := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega : 64 ≤ i)))
      simp [h1, h, show ¬ (i - 32 < 32) by omega, show i - 32 + 32 = i by omega]
  · simp [h1]

/-- The word of `z`. -/
def zWord (x : UInt64) : UInt64 := x &&& 0xFFFFFFFF00000000

theorem zWord_toNat (x : UInt64) : (zWord x).toNat = x.toNat / 2 ^ 32 * 2 ^ 32 := by
  rw [zWord, UInt64.toNat_and]
  have hc : (0xFFFFFFFF00000000 : UInt64).toNat = 18446744069414584320 := rfl
  rw [hc]
  exact land_mask x.toNat x.toNat_lt

theorem zWord_fields (x : UInt64) :
    Wasm.IEEE64.sign (zWord x) = Wasm.IEEE64.sign x ∧
      Wasm.IEEE64.exponent (zWord x) = Wasm.IEEE64.exponent x ∧
      Wasm.IEEE64.fraction (zWord x) = Wasm.IEEE64.fraction x / 2 ^ 32 * 2 ^ 32 := by
  have h := zWord_toNat x
  have hx := x.toNat_lt
  have hsz : UInt64.size = 18446744073709551616 := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold Wasm.IEEE64.sign
    rw [h]
    by_cases h1 : 2 ^ 63 ≤ x.toNat
    · have h2 : 2 ^ 63 ≤ x.toNat / 2 ^ 32 * 2 ^ 32 := by omega
      simp only [h1, h2, decide_true]
    · have h2 : ¬ 2 ^ 63 ≤ x.toNat / 2 ^ 32 * 2 ^ 32 := by omega
      simp only [h1, h2, decide_false]
  · simp only [Wasm.IEEE64.exponent, h]
    omega
  · simp only [Wasm.IEEE64.fraction, h]
    omega

/-- The facts about `z` for a positive normal `x` below `32`. -/
theorem z_facts (X : UInt64) (hX : Finite X) (hlo : 1 ≤ value X) (hhi : value X < 32) :
    Finite (zWord X) ∧ Wasm.IEEE64.sign (zWord X) = false ∧
      1023 ≤ Wasm.IEEE64.exponent X ∧ Wasm.IEEE64.exponent X ≤ 1027 ∧
      Wasm.IEEE64.scaledMagnitude (zWord X) =
        (2 ^ 20 + Wasm.IEEE64.fraction X / 2 ^ 32) * 2 ^ (Wasm.IEEE64.exponent X + 31) ∧
      2 ^ 20 + Wasm.IEEE64.fraction X / 2 ^ 32 < 2 ^ 21 ∧
      0 < value (zWord X) ∧ value (zWord X) ≤ value X ∧
      value X - value (zWord X) ≤ value X / 2 ^ 20 := by
  obtain ⟨hs, he, hf⟩ := zWord_fields X
  have h1022 : (1 : ℝ) / 2 ^ 1022 < 1 := by norm_num
  have hnorm := F64Magnitude.normal_of_value X (by linarith)
  have he1 : 1023 ≤ Wasm.IEEE64.exponent X :=
    F64Magnitude.exponent_ge_of_value X 1023 (by norm_num) (by norm_num; linarith)
  have he2 : Wasm.IEEE64.exponent X ≤ 1027 := by
    by_contra h
    have h2 := F64Magnitude.value_ge_of_exponent X 1028 5 (by norm_num) (by norm_num) (by norm_num)
      hnorm.2 (by omega)
    norm_num at h2
    linarith
  have hfX : Wasm.IEEE64.fraction X < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hzs : Wasm.IEEE64.sign (zWord X) = false := by rw [hs]; exact hnorm.2
  have hvX := F64Magnitude.normal_value X hnorm.2 (by omega)
  have hvZ := F64Magnitude.normal_value (zWord X) hzs (by rw [he]; omega)
  rw [he, hf] at hvZ
  have hzf : Finite (zWord X) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, he, bne_iff_ne, ne_eq]
    omega
  have h0 : (Wasm.IEEE64.exponent X == 0) = false := beq_false_of_ne (by omega)
  have h0' : (Wasm.IEEE64.exponent (zWord X) == 0) = false := beq_false_of_ne (by rw [he]; omega)
  have hmZ' : Wasm.IEEE64.scaledMagnitude (zWord X) =
      (2 ^ 52 + Wasm.IEEE64.fraction X / 2 ^ 32 * 2 ^ 32) * 2 ^ (Wasm.IEEE64.exponent X - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, he, hf, h0, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨e, hed⟩ : ∃ e, Wasm.IEEE64.exponent X = e := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, Wasm.IEEE64.fraction X = f := ⟨_, rfl⟩
  rw [hed] at he1 he2 hvX hvZ hmZ' ⊢
  rw [hfdef] at hfX hvX hvZ hmZ' ⊢
  have hmZ : Wasm.IEEE64.scaledMagnitude (zWord X) = (2 ^ 20 + f / 2 ^ 32) * 2 ^ (e + 31) := by
    rw [hmZ', show e + 31 = 32 + (e - 1) by omega, pow_add]
    ring
  obtain ⟨g, hg⟩ : ∃ g, f / 2 ^ 32 * 2 ^ 32 = g := ⟨_, rfl⟩
  have hgf : g ≤ f := hg ▸ Nat.div_mul_le_self f _
  have hfg : f - g < 2 ^ 32 := by rw [← hg]; omega
  rw [hg] at hvZ
  set P : ℝ := (2 : ℝ) ^ (e - 1) with hP
  have hP0 : 0 < P := by positivity
  have hgr : (g : ℝ) ≤ f := by exact_mod_cast hgf
  have hfgr : (f : ℝ) - g ≤ 2 ^ 32 := by
    have : ((f - g : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hfg.le
    rw [Nat.cast_sub hgf] at this
    exact this
  have hf0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  refine ⟨hzf, hzs, he1, he2, hmZ, by omega, ?_, ?_, ?_⟩
  · rw [hvZ]
    apply div_pos (mul_pos (by linarith [show (0 : ℝ) < 2 ^ 52 by norm_num]) hP0)
    norm_num
  · rw [hvX, hvZ]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right (by linarith) hP0.le
  · rw [hvX, hvZ, ← sub_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (((2 : ℝ) ^ 52 + f) * P - (2 ^ 52 + g) * P) * (2 ^ 1074 * 2 ^ 20) =
        ((f : ℝ) - g) * 2 ^ 20 * (P * 2 ^ 1074) := by ring
    rw [h3]
    have h4 : ((f : ℝ) - g) * 2 ^ 20 ≤ 2 ^ 52 + f := by
      have : ((f : ℝ) - g) * 2 ^ 20 ≤ 2 ^ 32 * 2 ^ 20 :=
        mul_le_mul_of_nonneg_right hfgr (by norm_num)
      have h5 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
      linarith [show (2 : ℝ) ^ 32 * 2 ^ 20 = 2 ^ 52 by norm_num]
    have h6 : ((f : ℝ) - g) * 2 ^ 20 * (P * 2 ^ 1074) ≤ (2 ^ 52 + f) * (P * 2 ^ 1074) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    linarith

/-- The word of `0.5625`. -/
theorem c0625_value : value (0x3FE2000000000000 : UInt64) = 9 / 16 := by
  have h : Wasm.IEEE64.scaledValue (0x3FE2000000000000 : UInt64) = 9 * 2 ^ 1070 := by
    decide +kernel
  rw [value, h]
  norm_num

/-- `-z z - 0.5625` is exact. -/
theorem arg1_exact (X : UInt64) (hX : Finite X) (hlo : 1 ≤ value X) (hhi : value X < 32) :
    Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
      0x3FE2000000000000) ∧
    value (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
      0x3FE2000000000000) = -(value (zWord X)) ^ 2 - 9 / 16 := by
  obtain ⟨hzf, hzs, he1, he2, hmZ, hm21, hz0, hzx, _⟩ := z_facts X hX hlo hhi
  set e := Wasm.IEEE64.exponent X
  set m := 2 ^ 20 + Wasm.IEEE64.fraction X / 2 ^ 32
  have hnf := F64NegateOps.finite_negate _ hzf
  have hnm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate (zWord X)) = m * 2 ^ (e + 31) := by
    rw [F64NegateOps.scaledMagnitude_negate, hmZ]
  have hmm : m * m < 2 ^ 53 := by
    have : m * m < 2 ^ 21 * 2 ^ 21 := Nat.mul_lt_mul'' hm21 hm21
    omega
  obtain ⟨hpf, hpv, hpm, hps⟩ := F64ExactProduct.mul_exact_scaled _ _ hnf hzf m m (e + 31) (e + 31)
    hnm hmZ hmm (by omega) (by omega)
  have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate (zWord X)) = true := by
    rw [(F64Sign.fields_negate _).2.2, hzs]
    rfl
  rw [hns, hzs] at hps
  have hcf : Finite (0x3FE2000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide
  have hcs : Wasm.IEEE64.scaledValue (0x3FE2000000000000 : UInt64) = 9 * 2 ^ 1070 := by
    decide +kernel
  have hpsv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X)) =
      -(((m * m) * 2 ^ (e + 31 + (e + 31) - 1074) : ℕ) : Int) := by
    have hb : (true != false) = true := rfl
    simp only [Wasm.IEEE64.scaledValue, hpm, hps, hb, ↓reduceIte]
  have hvn : value (Wasm.IEEE64.negate (zWord X)) = -value (zWord X) := by
    simp only [value, F64NegateOps.scaledValue_negate, Int.cast_neg, neg_div]
  have h := sub_exact_grid _ _ hpf hcf 1034 (by norm_num) (by
    rw [hpsv]
    apply Dvd.dvd.neg_right
    have h1 : (2 : ℕ) ^ 1034 ∣ (m * m) * 2 ^ (e + 31 + (e + 31) - 1074) :=
      Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
    exact_mod_cast Int.natCast_dvd_natCast.mpr h1) (by
    rw [hcs]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by norm_num)) _) (by
    have hvP : (Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X)) : ℝ) =
        -(value (zWord X)) ^ 2 * 2 ^ 1074 := by
      have h1 : value (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X)) =
          -(value (zWord X)) ^ 2 := by rw [hpv, hvn]; ring
      rw [value, div_eq_iff (by positivity)] at h1
      exact h1
    have hvC : (Wasm.IEEE64.scaledValue (0x3FE2000000000000 : UInt64) : ℝ) = 9 / 16 * 2 ^ 1074 := by
      have h1 := c0625_value
      rw [value, div_eq_iff (by positivity)] at h1
      exact h1
    have hz2 : value (zWord X) ^ 2 ≤ 1024 := by
      have h32 : value (zWord X) ≤ 32 := by linarith
      have := pow_le_pow_left₀ hz0.le h32 2
      norm_num at this ⊢
      exact this
    have hr : |(Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X))
        (zWord X)) : ℝ) - (Wasm.IEEE64.scaledValue (0x3FE2000000000000 : UInt64) : ℝ)| ≤
        (2 : ℝ) ^ 53 * 2 ^ 1034 := by
      rw [hvP, hvC, show -value (zWord X) ^ 2 * (2 : ℝ) ^ 1074 - 9 / 16 * 2 ^ 1074 =
        -((value (zWord X) ^ 2 + 9 / 16) * 2 ^ 1074) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
      have h2 : (value (zWord X) ^ 2 + 9 / 16) * (2 : ℝ) ^ 1074 ≤ 2 ^ 13 * 2 ^ 1074 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h3 : (2 : ℝ) ^ 13 * 2 ^ 1074 = 2 ^ 53 * 2 ^ 1034 := by
        rw [← pow_add, ← pow_add]
      linarith
    exact_mod_cast hr)
  refine ⟨h.1, ?_⟩
  rw [h.2, hpv, hvn, c0625_value]
  ring

/-- `z - x` is exact. -/
theorem d1_exact (X : UInt64) (hX : Finite X) (hlo : 1 ≤ value X) (hhi : value X < 32) :
    Finite (Wasm.IEEE64.sub (zWord X) X) ∧
      value (Wasm.IEEE64.sub (zWord X) X) = value (zWord X) - value X := by
  obtain ⟨hzf, hzs, he1, he2, _, _, _, _, _⟩ := z_facts X hX hlo hhi
  have h1022 : (1 : ℝ) / 2 ^ 1022 < 1 := by norm_num
  have hnorm := F64Magnitude.normal_of_value X (by linarith)
  obtain ⟨_, he, hf⟩ := zWord_fields X
  have h0 : (Wasm.IEEE64.exponent X == 0) = false := beq_false_of_ne (by omega)
  have h0' : (Wasm.IEEE64.exponent (zWord X) == 0) = false := beq_false_of_ne (by rw [he]; omega)
  have hsX : Wasm.IEEE64.scaledValue X =
      (((2 ^ 52 + Wasm.IEEE64.fraction X) * 2 ^ (Wasm.IEEE64.exponent X - 1) : ℕ) : Int) := by
    simp only [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hnorm.2, h0,
      Bool.false_eq_true, ↓reduceIte]
  have hsZ : Wasm.IEEE64.scaledValue (zWord X) =
      (((2 ^ 52 + Wasm.IEEE64.fraction X / 2 ^ 32 * 2 ^ 32) * 2 ^ (Wasm.IEEE64.exponent X - 1) : ℕ) :
        Int) := by
    simp only [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hzs, he, hf, h0,
      Bool.false_eq_true, ↓reduceIte]
  obtain ⟨e, hed⟩ : ∃ e, Wasm.IEEE64.exponent X = e := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, Wasm.IEEE64.fraction X = f := ⟨_, rfl⟩
  rw [hed] at he1 he2 hsX hsZ
  rw [hfdef] at hsX hsZ
  obtain ⟨g, hg⟩ : ∃ g, f / 2 ^ 32 * 2 ^ 32 = g := ⟨_, rfl⟩
  have hgf : g ≤ f := hg ▸ Nat.div_mul_le_self f _
  have hfg : f - g < 2 ^ 32 := by rw [← hg]; omega
  rw [hg] at hsZ
  have hdZ : (2 : ℕ) ^ (e - 1) ∣ (2 ^ 52 + g) * 2 ^ (e - 1) := Dvd.intro_left _ rfl
  have hdX : (2 : ℕ) ^ (e - 1) ∣ (2 ^ 52 + f) * 2 ^ (e - 1) := Dvd.intro_left _ rfl
  have h := sub_exact_grid _ _ hzf hX (e - 1) (by omega) (by
    rw [hsZ]
    exact_mod_cast Int.natCast_dvd_natCast.mpr hdZ) (by
    rw [hsX]
    exact_mod_cast Int.natCast_dvd_natCast.mpr hdX) (by
    rw [hsZ, hsX]
    have h1 : (((2 ^ 52 + g) * 2 ^ (e - 1) : ℕ) : Int) - (((2 ^ 52 + f) * 2 ^ (e - 1) : ℕ) : Int) =
        -(((f - g : ℕ) : Int) * 2 ^ (e - 1)) := by
      rw [Nat.cast_sub hgf]
      push_cast
      ring
    have hp0 : (0 : Int) ≤ ((f - g : ℕ) : Int) * 2 ^ (e - 1) :=
      mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)
    rw [h1, abs_neg, abs_of_nonneg hp0]
    have h2 : ((f - g : ℕ) : Int) ≤ 2 ^ 53 := by
      have h3 : f - g ≤ 2 ^ 53 := by omega
      have h4 : ((f - g : ℕ) : Int) ≤ ((2 ^ 53 : ℕ) : Int) := Int.ofNat_le.mpr h3
      simpa using h4
    exact mul_le_mul_of_nonneg_right h2 (pow_nonneg (by norm_num) _))
  exact h

#print axioms land_mask
#print axioms zWord_fields
#print axioms z_facts
#print axioms arg1_exact
#print axioms d1_exact

end Verified.Examples.ErfTailSplit
