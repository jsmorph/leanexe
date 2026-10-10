import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64ExponentBounds
import LeanExe.ProofKit.F64Source

/-!
Exact operations.  A finite word's magnitude is `M · 2 ^ (e - 1)` scaled units with `M < 2 ^ 53`
for its exponent field `e`, so two positive words within a factor of two of each other differ by a
multiple of the smaller grid of at most `2 ^ 53` units, and their rounded difference is exact
(Sterbenz's lemma).  Multiplication of a normal word by `2.0` adds one to its exponent field and is
exact while the field stays finite.
-/

namespace LeanExe.ProofKit.F64Exact
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem magnitude_grid (x : UInt64) :
    ∃ M : ℕ, M < 2 ^ 53 ∧
      Wasm.IEEE64.scaledMagnitude x = M * 2 ^ (Wasm.IEEE64.exponent x - 1) := by
  have hf : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  by_cases he : Wasm.IEEE64.exponent x = 0
  · refine ⟨Wasm.IEEE64.fraction x, by omega, ?_⟩
    simp [Wasm.IEEE64.scaledMagnitude, he]
  · refine ⟨2 ^ 52 + Wasm.IEEE64.fraction x, by omega, ?_⟩
    simp [Wasm.IEEE64.scaledMagnitude, he]

theorem scaledValue_of_sign (x : UInt64) (hs : Wasm.IEEE64.sign x = false) :
    Wasm.IEEE64.scaledValue x = (Wasm.IEEE64.scaledMagnitude x : Int) := by
  simp [Wasm.IEEE64.scaledValue, hs]

/-- Sterbenz's lemma in scaled units. -/
theorem sub_sterbenz (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hsa : Wasm.IEEE64.sign a = false) (hsb : Wasm.IEEE64.sign b = false)
    (h1 : Wasm.IEEE64.scaledMagnitude b ≤ 2 * Wasm.IEEE64.scaledMagnitude a)
    (h2 : Wasm.IEEE64.scaledMagnitude a ≤ 2 * Wasm.IEEE64.scaledMagnitude b)
    (hea : Wasm.IEEE64.exponent a ≤ 2040) (heb : Wasm.IEEE64.exponent b ≤ 2040) :
    Finite (Wasm.IEEE64.sub a b) ∧
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.sub a b) =
        Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b := by
  obtain ⟨Ma, hMa, hma⟩ := magnitude_grid a
  obtain ⟨Mb, hMb, hmb⟩ := magnitude_grid b
  rw [scaledValue_of_sign a hsa, scaledValue_of_sign b hsb]
  rw [hma, hmb] at h1 h2
  rw [hma, hmb]
  set ga := Wasm.IEEE64.exponent a - 1 with hga
  set gb := Wasm.IEEE64.exponent b - 1 with hgb
  have hp : ∀ g : ℕ, 0 < 2 ^ g := fun g => by positivity
  rcases le_total ga gb with hg | hg
  · set D := Mb * 2 ^ (gb - ga) with hD
    have hmbD : Mb * 2 ^ gb = D * 2 ^ ga := by
      rw [hD, mul_assoc, ← pow_add, show gb - ga + ga = gb by omega]
    rw [hmbD] at h1 h2
    have hD1 : D ≤ 2 * Ma := by
      apply Nat.le_of_mul_le_mul_right (c := 2 ^ ga) _ (hp ga)
      calc D * 2 ^ ga ≤ 2 * (Ma * 2 ^ ga) := h1
        _ = 2 * Ma * 2 ^ ga := by ring
    have hD2 : Ma ≤ 2 * D := by
      apply Nat.le_of_mul_le_mul_right (c := 2 ^ ga) _ (hp ga)
      calc Ma * 2 ^ ga ≤ 2 * (D * 2 ^ ga) := h2
        _ = 2 * D * 2 ^ ga := by ring
    have h := F64GridExact.sub_grid_exact a b ha hb ((Ma : Int) - (D : Int)) ga
      (by rw [scaledValue_of_sign a hsa, scaledValue_of_sign b hsb, hma, hmb, hmbD]; push_cast; ring)
      (by omega) (by have := hea; omega)
    rw [scaledValue_of_sign a hsa, scaledValue_of_sign b hsb, hma, hmb, hmbD] at h
    rw [hmbD]
    exact h
  · set D := Ma * 2 ^ (ga - gb) with hD
    have hmaD : Ma * 2 ^ ga = D * 2 ^ gb := by
      rw [hD, mul_assoc, ← pow_add, show ga - gb + gb = ga by omega]
    rw [hmaD] at h1 h2
    have hD1 : Mb ≤ 2 * D := by
      apply Nat.le_of_mul_le_mul_right (c := 2 ^ gb) _ (hp gb)
      calc Mb * 2 ^ gb ≤ 2 * (D * 2 ^ gb) := h1
        _ = 2 * D * 2 ^ gb := by ring
    have hD2 : D ≤ 2 * Mb := by
      apply Nat.le_of_mul_le_mul_right (c := 2 ^ gb) _ (hp gb)
      calc D * 2 ^ gb ≤ 2 * (Mb * 2 ^ gb) := h2
        _ = 2 * Mb * 2 ^ gb := by ring
    have h := F64GridExact.sub_grid_exact a b ha hb ((D : Int) - (Mb : Int)) gb
      (by rw [scaledValue_of_sign a hsa, scaledValue_of_sign b hsb, hma, hmb, hmaD]; push_cast; ring)
      (by omega) (by have := heb; omega)
    rw [scaledValue_of_sign a hsa, scaledValue_of_sign b hsb, hma, hmb, hmaD] at h
    rw [hmaD]
    exact h

theorem sign_of_pos (x : UInt64) (hx : 0 < value x) : Wasm.IEEE64.sign x = false := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x) with h0 | h0
    · have : value x = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h0]
        split <;> simp
      linarith
    · exact h0
  cases hs : Wasm.IEEE64.sign x
  · rfl
  · have := (F64Magnitude.sign_value x hmag).mp hs
    linarith

theorem value_of_sign (x : UInt64) (hs : Wasm.IEEE64.sign x = false) :
    value x = (Wasm.IEEE64.scaledMagnitude x : ℝ) / 2 ^ 1074 := by
  rw [value, scaledValue_of_sign x hs]
  push_cast
  ring

theorem exponent_le_of_value (x : UInt64) (hx : |value x| < 2 ^ 900) :
    Wasm.IEEE64.exponent x ≤ 2040 := by
  have hb := F64PositiveSpacing.boundary_value 2041 (by norm_num) (by norm_num)
  have h : |value x| < |value (F64ExponentBounds.boundary 2041)| := by
    rw [show F64ExponentBounds.boundary 2041 = UInt64.ofNat (2041 * 2 ^ 52) from rfl, hb]
    rw [abs_of_pos (show (0 : ℝ) < 2 ^ (2041 + 51) / 2 ^ 1074 by positivity)]
    calc |value x| < 2 ^ 900 := hx
      _ ≤ (2 : ℝ) ^ (2041 + 51) / 2 ^ 1074 := by norm_num
  have := F64ExponentBounds.exponent_lt_of_magnitude_lt x 2041 (by norm_num) h
  omega

/-- Sterbenz's lemma: the difference of positive words within a factor of two is exact. -/
theorem sub_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (hpa : 0 < value a)
    (hpb : 0 < value b) (h1 : value b ≤ 2 * value a) (h2 : value a ≤ 2 * value b)
    (hla : value a < 2 ^ 900) (hlb : value b < 2 ^ 900) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  have hsa := sign_of_pos a hpa
  have hsb := sign_of_pos b hpb
  have hva := value_of_sign a hsa
  have hvb := value_of_sign b hsb
  have hN1 : Wasm.IEEE64.scaledMagnitude b ≤ 2 * Wasm.IEEE64.scaledMagnitude a := by
    rw [hva, hvb] at h1
    have : (Wasm.IEEE64.scaledMagnitude b : ℝ) ≤ 2 * (Wasm.IEEE64.scaledMagnitude a : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
      field_simp at h
      linarith
    exact_mod_cast this
  have hN2 : Wasm.IEEE64.scaledMagnitude a ≤ 2 * Wasm.IEEE64.scaledMagnitude b := by
    rw [hva, hvb] at h2
    have : (Wasm.IEEE64.scaledMagnitude a : ℝ) ≤ 2 * (Wasm.IEEE64.scaledMagnitude b : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
      field_simp at h
      linarith
    exact_mod_cast this
  have hea := exponent_le_of_value a (by rw [abs_of_pos hpa]; exact hla)
  have heb := exponent_le_of_value b (by rw [abs_of_pos hpb]; exact hlb)
  have h := sub_sterbenz a b ha hb hsa hsb hN1 hN2 hea heb
  refine ⟨h.1, ?_⟩
  rw [value, h.2, value, value]
  push_cast
  ring

theorem two_word : Wasm.IEEE64.encodeFinite false 1024 0 = 0x4000000000000000 := by decide

/-- Doubling a normal word is exact. -/
theorem mul_two_exact (y : UInt64) (hy : Finite y) (hye : 1 ≤ Wasm.IEEE64.exponent y)
    (hy2 : Wasm.IEEE64.exponent y ≤ 2040) :
    Finite (Wasm.IEEE64.mul 0x4000000000000000 y) ∧
      value (Wasm.IEEE64.mul 0x4000000000000000 y) = 2 * value y := by
  have h := F64PowerScale.mul_power 1024 y (by norm_num) (by norm_num) hy hye (by omega)
  rw [two_word] at h
  have hc : ¬ (0x7FF ≤ Wasm.IEEE64.exponent y + 1024 - 1023) := by omega
  simp only [hc, ite_false] at h
  have he : Wasm.IEEE64.exponent y + 1024 - 1023 = Wasm.IEEE64.exponent y + 1 := by omega
  rw [he] at h
  have hf : Wasm.IEEE64.fraction y < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hE := F64Source.exponent_encodeFinite (Wasm.IEEE64.sign y) (Wasm.IEEE64.exponent y + 1)
    (Wasm.IEEE64.fraction y) (by omega) hf
  have hF := F64Source.fraction_encodeFinite (Wasm.IEEE64.sign y) (Wasm.IEEE64.exponent y + 1)
    (Wasm.IEEE64.fraction y) (by omega) hf
  have hS := F64Source.sign_encodeFinite (Wasm.IEEE64.sign y) (Wasm.IEEE64.exponent y + 1)
    (Wasm.IEEE64.fraction y) (by omega) hf
  rw [h]
  refine ⟨?_, ?_⟩
  · simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hE, bne_iff_ne, ne_eq]
    omega
  · simp only [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, hE, hF, hS]
    have h1 : (Wasm.IEEE64.exponent y + 1 == 0) = false := by simp
    have h2 : (Wasm.IEEE64.exponent y == 0) = false := by simp; omega
    simp only [h1, h2, Bool.false_eq_true, ite_false, Nat.add_sub_cancel]
    have hp : (2 : ℕ) ^ Wasm.IEEE64.exponent y = 2 * 2 ^ (Wasm.IEEE64.exponent y - 1) := by
      rw [← pow_succ', show Wasm.IEEE64.exponent y - 1 + 1 = Wasm.IEEE64.exponent y by omega]
    rw [hp]
    split <;> push_cast <;> ring

/-- Halving a word whose exponent field is at least 2 is exact. -/
theorem mul_half_exact (y : UInt64) (hy : Finite y) (hye : 2 ≤ Wasm.IEEE64.exponent y) :
    Finite (Wasm.IEEE64.mul 0x3FE0000000000000 y) ∧
      value (Wasm.IEEE64.mul 0x3FE0000000000000 y) = value y / 2 := by
  have hy2 : Wasm.IEEE64.exponent y < 2047 := by
    have h := hy
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hw : Wasm.IEEE64.encodeFinite false 1022 0 = 0x3FE0000000000000 := by decide
  have h := F64PowerScale.mul_power_finite 1022 y (by norm_num) (by norm_num) hy (by omega)
    (by omega) (by omega)
  rw [hw] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, show ((1022 : ℕ) : ℤ) - 1023 = -1 by norm_num, zpow_neg_one]
  ring

/-- A word of magnitude at least `2 ^ -1000` has exponent field at least 2. -/
theorem exponent_two_of_value (w : UInt64) (h : 1 / 2 ^ 1000 ≤ |value w|) :
    2 ≤ Wasm.IEEE64.exponent w := by
  by_contra hn
  have := F64Magnitude.magnitude_lt w 2 (-1021) (by norm_num) (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (-1021 : ℤ) < 1 / 2 ^ 1000 := by norm_num
  exact absurd h (not_le.mpr (this.trans h2))

#print axioms magnitude_grid
#print axioms sub_sterbenz
#print axioms sub_exact
#print axioms mul_two_exact
#print axioms mul_half_exact

end LeanExe.ProofKit.F64Exact
