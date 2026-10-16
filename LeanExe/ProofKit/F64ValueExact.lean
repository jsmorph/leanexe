import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64Magnitude

/-!
Exactness of sums and differences stated with values.  A finite word of magnitude at least
`2 ^ (52 + s)` scaled units is a multiple of `2 ^ s` scaled units, and a sum or difference of two
such multiples within `2 ^ (53 + s)` scaled units is exact.
-/

namespace LeanExe.ProofKit.F64ValueExact

open CodeLib.IEEE64

theorem scaled_eq (v : UInt64) : (Wasm.IEEE64.scaledValue v : ℝ) = value v * 2 ^ 1074 := by
  simp only [value]
  field_simp

/-- A finite word of magnitude at least `2 ^ (52 + s)` scaled units is a multiple of `2 ^ s`
scaled units. -/
theorem dvd_of_value (v : UInt64) (hv : Finite v) (s : Nat)
    (h : (2 : ℝ) ^ (52 + s) / 2 ^ 1074 ≤ |value v|) :
    (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue v := by
  have hm : (2 : ℝ) ^ (52 + s) ≤ (Wasm.IEEE64.scaledMagnitude v : ℝ) := by
    have habs : |(Wasm.IEEE64.scaledValue v : ℝ)| = (Wasm.IEEE64.scaledMagnitude v : ℝ) := by
      simp only [Wasm.IEEE64.scaledValue]
      split <;> simp
    rw [← habs, scaled_eq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    rwa [div_le_iff₀ (by positivity)] at h
  have hm' : 2 ^ (52 + s) ≤ Wasm.IEEE64.scaledMagnitude v := by exact_mod_cast hm
  have hf : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hdvd : 2 ^ s ∣ Wasm.IEEE64.scaledMagnitude v := by
    unfold Wasm.IEEE64.scaledMagnitude at hm' ⊢
    by_cases he : Wasm.IEEE64.exponent v = 0
    · simp only [he, beq_self_eq_true, ite_true] at hm'
      have : 2 ^ 52 ≤ 2 ^ (52 + s) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · simp only [show (Wasm.IEEE64.exponent v == 0) = false by simpa using he,
        Bool.false_eq_true, ite_false] at hm' ⊢
      have hse : s ≤ Wasm.IEEE64.exponent v - 1 := by
        by_contra hlt
        have h1 : (2 ^ 52 + Wasm.IEEE64.fraction v) * 2 ^ (Wasm.IEEE64.exponent v - 1) <
            2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        have h2 : 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) ≤ 2 ^ (52 + s) := by
          rw [← pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hse) _
  have hz : ((2 : Nat) ^ s : Int) ∣ (Wasm.IEEE64.scaledMagnitude v : Int) :=
    Int.natCast_dvd_natCast.mpr hdvd
  push_cast at hz
  unfold Wasm.IEEE64.scaledValue
  split
  · exact (dvd_neg).mpr hz
  · exact hz

/-- A difference of two words on the grid of `2 ^ s` scaled units, within `2 ^ (53 + s)` scaled
units in magnitude, is exact. -/
theorem sub_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (s : Nat) (hs : s ≤ 2043)
    (hda : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue a)
    (hdb : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue b)
    (hbound : |value a - value b| ≤ (2 : ℝ) ^ (53 + s) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  apply F64ErrorTrack.sub_exact_grid a b ha hb s hs hda hdb
  have hr : |((Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b : Int) : ℝ)| ≤
      (2 : ℝ) ^ 53 * 2 ^ s := by
    push_cast
    rw [scaled_eq, scaled_eq, ← sub_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← pow_add]
    rwa [le_div_iff₀ (by positivity)] at hbound
  exact_mod_cast hr

/-- `sub_exact` for a sum. -/
theorem add_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (s : Nat) (hs : s ≤ 2043)
    (hda : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue a)
    (hdb : (2 : Int) ^ s ∣ Wasm.IEEE64.scaledValue b)
    (hbound : |value a + value b| ≤ (2 : ℝ) ^ (53 + s) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.add a b) ∧ value (Wasm.IEEE64.add a b) = value a + value b := by
  apply F64ErrorTrack.add_exact_grid a b ha hb s hs hda hdb
  have hr : |((Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b : Int) : ℝ)| ≤
      (2 : ℝ) ^ 53 * 2 ^ s := by
    push_cast
    rw [scaled_eq, scaled_eq, ← add_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← pow_add]
    rwa [le_div_iff₀ (by positivity)] at hbound
  exact_mod_cast hr

/-- The scaled value of a word whose value is a difference of two words' values. -/
theorem scaled_of_value_sub (a b c : UInt64) (h : value c = value a - value b) :
    Wasm.IEEE64.scaledValue c = Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b := by
  have hr : (Wasm.IEEE64.scaledValue c : ℝ) =
      (Wasm.IEEE64.scaledValue a : ℝ) - Wasm.IEEE64.scaledValue b := by
    rw [scaled_eq, scaled_eq, scaled_eq, h]
    ring
  exact_mod_cast hr

/-- The relative error of a rounded difference, as `F64AddBounds.sub_real_relative` gives it, in
the form used here. -/
theorem sub_rel (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hmax : |value a - value b| < 2 ^ 1023) :
    Finite (Wasm.IEEE64.sub a b) ∧
      |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤
        |value a - value b| / 2 ^ 53 := by
  obtain ⟨hf, he⟩ := F64AddBounds.sub_real_relative a b ha hb hmax
  refine ⟨hf, he.trans (le_of_eq ?_)⟩
  simp only [unitRoundoff64]
  ring

/-- `sub_rel` for a sum. -/
theorem add_rel (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hmax : |value a + value b| < 2 ^ 1023) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
        |value a + value b| / 2 ^ 53 := by
  obtain ⟨hf, he⟩ := F64AddBounds.add_real_relative a b ha hb hmax
  refine ⟨hf, he.trans (le_of_eq ?_)⟩
  simp only [unitRoundoff64]
  ring

#print axioms dvd_of_value
#print axioms sub_exact
#print axioms add_exact
#print axioms scaled_of_value_sub
#print axioms sub_rel
#print axioms add_rel

end LeanExe.ProofKit.F64ValueExact
