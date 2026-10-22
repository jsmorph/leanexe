import Library.Numerics.Float64.Tanh.Expm1ReduceConst
import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64Sign

/-!
Word facts of the reduction in fdlibm's `expm1`.  `diff_exact` and `sum_exact`: a difference or
sum of two words on the grid of `2 ^ g` scaled units is exact when it is below `2 ^ (53 + g)`
scaled units.  `mul_ln2Hi`: the product of an integer of magnitude at most 1024 and `ln2Hi`, whose
significand has 32 bits, is exact.  `convert_spec` and `truncSat_spec` give the integer
conversions in both directions.
-/

namespace Library.Numerics.Float64.Tanh.Expm1ReduceWords
open CodeLib.IEEE64 LeanExe.ProofKit Expm1ReduceConst

set_option exponentiation.threshold 4096

theorem scaled_dvd (a : UInt64) (g : Nat) (h : 2 ^ g ∣ Wasm.IEEE64.scaledMagnitude a) :
    (2 : ℤ) ^ g ∣ Wasm.IEEE64.scaledValue a := by
  obtain ⟨k, hk⟩ := h
  unfold Wasm.IEEE64.scaledValue
  split
  · exact ⟨-(k : ℤ), by simp only [hk]; push_cast; ring⟩
  · exact ⟨(k : ℤ), by simp only [hk]; push_cast; ring⟩

/-- An exact difference on the grid of `2 ^ g`. -/
theorem diff_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : Nat) (hg : g ≤ 2043)
    (hda : 2 ^ g ∣ Wasm.IEEE64.scaledMagnitude a) (hdb : 2 ^ g ∣ Wasm.IEEE64.scaledMagnitude b)
    (hbound : |value a - value b| ≤ (2 : ℝ) ^ (53 + g) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  obtain ⟨za, hza⟩ := scaled_dvd a g hda
  obtain ⟨zb, hzb⟩ := scaled_dvd b g hdb
  have hdiff : Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b = (za - zb) * 2 ^ g := by
    rw [hza, hzb]; ring
  have hz : (za - zb).natAbs ≤ 2 ^ 53 := by
    have h1 : value a - value b = ((za - zb : ℤ) : ℝ) * 2 ^ g / 2 ^ 1074 := by
      simp only [value, hza, hzb]; push_cast; ring
    rw [h1, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g), div_le_div_iff_of_pos_right (by positivity),
      pow_add, mul_le_mul_iff_of_pos_right (by positivity)] at hbound
    have : (((za - zb).natAbs : ℕ) : ℝ) ≤ (2 : ℝ) ^ 53 := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact hbound
    exact_mod_cast this
  obtain ⟨hf, hv⟩ := F64GridExact.sub_grid_exact a b ha hb _ g hdiff hz hg
  refine ⟨hf, ?_⟩
  simp only [value, hv]; push_cast; ring

/-- An exact sum on the grid of `2 ^ g`. -/
theorem sum_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (g : Nat) (hg : g ≤ 2043)
    (hda : 2 ^ g ∣ Wasm.IEEE64.scaledMagnitude a) (hdb : 2 ^ g ∣ Wasm.IEEE64.scaledMagnitude b)
    (hbound : |value a + value b| ≤ (2 : ℝ) ^ (53 + g) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.add a b) ∧ value (Wasm.IEEE64.add a b) = value a + value b := by
  obtain ⟨za, hza⟩ := scaled_dvd a g hda
  obtain ⟨zb, hzb⟩ := scaled_dvd b g hdb
  have hsum : Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b = (za + zb) * 2 ^ g := by
    rw [hza, hzb]; ring
  have hz : (za + zb).natAbs ≤ 2 ^ 53 := by
    have h1 : value a + value b = ((za + zb : ℤ) : ℝ) * 2 ^ g / 2 ^ 1074 := by
      simp only [value, hza, hzb]; push_cast; ring
    rw [h1, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g), div_le_div_iff_of_pos_right (by positivity),
      pow_add, mul_le_mul_iff_of_pos_right (by positivity)] at hbound
    have : (((za + zb).natAbs : ℕ) : ℝ) ≤ (2 : ℝ) ^ 53 := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact hbound
    exact_mod_cast this
  obtain ⟨hf, hv⟩ := F64GridExact.grid_add_exact a b ha hb _ g hsum hz hg
  refine ⟨hf, ?_⟩
  simp only [value, hv]; push_cast; ring

/-- A word of magnitude at least `2 ^ (g - 1022)` lies on the grid of `2 ^ g`. -/
theorem grid_of_magnitude (a : UInt64) (g : Nat) (h : (2 : ℝ) ^ (52 + g) / 2 ^ 1074 ≤ |value a|) :
    2 ^ g ∣ Wasm.IEEE64.scaledMagnitude a := by
  apply F64NearestSum.magnitude_dvd
  have hv : |value a| = (Wasm.IEEE64.scaledMagnitude a : ℝ) / 2 ^ 1074 := by
    rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      ← natAbs_scaledValue, Nat.cast_natAbs, Int.cast_abs]
  rw [hv, div_le_div_iff_of_pos_right (by positivity)] at h
  exact_mod_cast h

/-- `ln2Hi` is `2977044471 · 2 ^ -32`, on the grid of `2 ^ 1042` scaled units. -/
theorem ln2Hi_magnitude : Wasm.IEEE64.scaledMagnitude ln2Hi = 2977044471 * 2 ^ 1042 ∧
    Wasm.IEEE64.sign ln2Hi = false := by
  constructor <;> decide +kernel

/-- `convertI64U n` for `n < 2 ^ 53` is exact. -/
theorem convert_spec (n : UInt64) (hn : n.toNat < 2 ^ 53) :
    Finite (Wasm.IEEE64.convertI64U n) ∧
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.convertI64U n) = (n.toNat : ℤ) * 2 ^ 1074 := by
  have h := F64GridExact.signed_grid_packing_exact (n.toNat : ℤ) 1074
    (by rw [Int.natAbs_natCast]; omega) (by norm_num)
  rw [Int.natAbs_natCast] at h
  have hd : decide ((n.toNat : ℤ) < 0) = false := decide_eq_false (by omega)
  rw [hd] at h
  have hc : Wasm.IEEE64.convertI64U n =
      Wasm.IEEE64.roundScaledMagnitude false (n.toNat * 2 ^ 1074) := by
    unfold Wasm.IEEE64.convertI64U Wasm.IEEE64.fromInt
    rw [Int.natAbs_natCast, hd]
  rw [hc]
  exact h

/-- The product of `ln2Hi` and an integer word of magnitude at most 1024 is exact. -/
theorem mul_ln2Hi (t : UInt64) (htf : Finite t) (n : Nat) (hn : n ≤ 1024)
    (htm : Wasm.IEEE64.scaledMagnitude t = n * 2 ^ 1074) :
    Finite (Wasm.IEEE64.mul t ln2Hi) ∧
      value (Wasm.IEEE64.mul t ln2Hi) = value t * value ln2Hi := by
  obtain ⟨hLm, hLs⟩ := ln2Hi_magnitude
  have hN : n * 2977044471 < 2 ^ 53 := by omega
  have hprod : n * 2 ^ 1074 * (2977044471 * 2 ^ 1042) = (n * 2977044471) * 2 ^ (1074 + 1042) := by
    rw [pow_add]; ring
  rw [mul_finite_rounder t ln2Hi htf const_finite.1, htm, hLm, hprod,
    F64PowerScale.dyadic_shifted_exact _ _ _ hN]
  have hmax : n * 2977044471 * 2 ^ 1042 < 2 ^ 2097 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hN (by positivity)) (by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hp := F64PackRelative.pack_spec (Wasm.IEEE64.sign t != Wasm.IEEE64.sign ln2Hi) _ hmax
  have hr : roundedMagnitude (n * 2977044471 * 2 ^ 1042) = n * 2977044471 * 2 ^ 1042 :=
    F64GridExact.roundedMagnitude_shifted_small _ _ hN.le
  refine ⟨hp.1, ?_⟩
  set N := n * 2977044471 * 2 ^ 1042 with hNdef
  set w := Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign t != Wasm.IEEE64.sign ln2Hi) N
  have hsw : Wasm.IEEE64.scaledValue w =
      if Wasm.IEEE64.sign t then -(N : ℤ) else (N : ℤ) := by
    unfold Wasm.IEEE64.scaledValue
    rw [hp.2.1, hr, hp.2.2, hLs]
    cases Wasm.IEEE64.sign t <;> rfl
  have hst : Wasm.IEEE64.scaledValue t =
      if Wasm.IEEE64.sign t then -((n * 2 ^ 1074 : ℕ) : ℤ) else ((n * 2 ^ 1074 : ℕ) : ℤ) := by
    unfold Wasm.IEEE64.scaledValue
    rw [htm]
  have hsL : Wasm.IEEE64.scaledValue ln2Hi = ((2977044471 * 2 ^ 1042 : ℕ) : ℤ) := by
    unfold Wasm.IEEE64.scaledValue
    rw [hLm, hLs]
    rfl
  have hNr : (N : ℝ) = n * 2977044471 * 2 ^ 1042 := by rw [hNdef]; push_cast; ring
  rw [value, value, value, hsw, hst, hsL]
  cases Wasm.IEEE64.sign t
  · simp only [Bool.false_eq_true, ite_false, Int.cast_natCast]
    rw [hNr]; push_cast; field_simp; ring
  · simp only [ite_true, Int.cast_neg, Int.cast_natCast]
    rw [hNr]; push_cast; field_simp; ring

/-- Unsigned truncation of a nonnegative word below `2 ^ 62` is the floor of its value. -/
theorem truncSat_spec (q : UInt64) (hqf : Finite q) (hs : Wasm.IEEE64.sign q = false)
    (hq : value q < 2 ^ 62) :
    ((Wasm.IEEE64.truncSatI64U q).toNat : ℝ) ≤ value q ∧
      value q < (Wasm.IEEE64.truncSatI64U q).toNat + 1 ∧
      (Wasm.IEEE64.truncSatI64U q).toNat < 2 ^ 62 := by
  set M := Wasm.IEEE64.scaledMagnitude q
  have hv : value q = (M : ℝ) / 2 ^ 1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hs, M]
  have hK : (M / 2 ^ 1074 : ℕ) < 2 ^ 62 := by
    rw [hv, div_lt_iff₀ (by positivity)] at hq
    have : (M : ℝ) < 2 ^ 62 * 2 ^ 1074 := hq
    have h2 : M < 2 ^ 62 * 2 ^ 1074 := by exact_mod_cast this
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
  have hfin : Wasm.IEEE64.isFinite q = true := hqf
  have htr : Wasm.IEEE64.truncatedInt q = some ((M / 2 ^ 1074 : ℕ) : ℤ) := by
    unfold Wasm.IEEE64.truncatedInt
    rw [ite_eq_left hfin]
    simp [hs, M]
  have hKw : (Wasm.IEEE64.truncSatI64U q).toNat = M / 2 ^ 1074 := by
    unfold Wasm.IEEE64.truncSatI64U
    rw [not_nan_of_finite hqf]
    simp only [Bool.false_eq_true, ite_false, htr]
    by_cases h0 : M / 2 ^ 1074 = 0
    · rw [ite_eq_left (by rw [h0]; norm_num), h0]; rfl
    · have hpos : ¬ ((M / 2 ^ 1074 : ℕ) : ℤ) ≤ 0 := by omega
      have hlt : ¬ (2 : ℤ) ^ 64 - 1 ≤ ((M / 2 ^ 1074 : ℕ) : ℤ) := by
        have : ((M / 2 ^ 1074 : ℕ) : ℤ) < 2 ^ 62 := by exact_mod_cast hK
        linarith
      rw [ite_eq_right hpos, ite_eq_right hlt]
      unfold Wasm.IEEE64.intToUInt64
      rw [ite_eq_right (by omega), Int.natAbs_natCast]
      exact UInt64.toNat_ofNat_of_lt' (lt_trans hK (by norm_num))
  rw [hKw]
  refine ⟨?_, ?_, hK⟩
  · rw [hv, le_div_iff₀ (by positivity)]
    have := Nat.div_mul_le_self M (2 ^ 1074)
    exact_mod_cast this
  · rw [hv, div_lt_iff₀ (by positivity)]
    have := Nat.lt_div_mul_add (a := M) (b := 2 ^ 1074) (by positivity)
    have h2 : M < (M / 2 ^ 1074 + 1) * 2 ^ 1074 := by
      rw [Nat.add_mul, one_mul]; exact this
    exact_mod_cast h2

#print axioms diff_exact
#print axioms sum_exact
#print axioms grid_of_magnitude
#print axioms convert_spec
#print axioms mul_ln2Hi
#print axioms truncSat_spec

end Library.Numerics.Float64.Tanh.Expm1ReduceWords
