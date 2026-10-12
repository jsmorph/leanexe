import Verified.Examples.TanWords
import Verified.Examples.TrigNearest
import Verified.Examples.TrigFloatTools
import Verified.Examples.TrigSmall
import LeanExe.ProofKit.F64ExactProduct

/-!
The truncation of a word to its high 32 bits, which `Tan.kernelTan` uses to split `w` and
`-1/w` into a head of 21 significant bits and a tail: the head keeps the sign and exponent, lies
within `2 ^ -20` relative of the word, and the product of two heads is exact.  Sterbenz's lemma
gives the exact difference of two words of the same sign within a factor of two.
-/

namespace Verified.Examples.TanTrunc

open CodeLib.IEEE64 LeanExe.ProofKit TanWords

def mask : UInt64 := 0xFFFFFFFF00000000

theorem high_mask (n : Nat) (hn : n < 2 ^ 64) : n &&& 0xFFFFFFFF00000000 = n / 2 ^ 32 * 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (0xFFFFFFFF00000000 : Nat) = (2 ^ 32 - 1) * 2 ^ 32 by norm_num,
    Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : 32 ≤ i
  · have : i - 32 + 32 = i := by omega
    rw [this]
    by_cases h2 : i < 64
    · simp [h1, show i - 32 < 32 by omega]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1, this, show ¬ i - 32 < 32 by omega]
  · simp [h1]

theorem mask_toNat (w : UInt64) : (w &&& mask).toNat = w.toNat / 2 ^ 32 * 2 ^ 32 := by
  rw [UInt64.toNat_and, show mask.toNat = 0xFFFFFFFF00000000 from rfl]
  exact high_mask _ w.toNat_lt

/-- The fields of a truncated word. -/
theorem trunc_fields (w : UInt64) :
    Wasm.IEEE64.exponent (w &&& mask) = Wasm.IEEE64.exponent w ∧
      Wasm.IEEE64.sign (w &&& mask) = Wasm.IEEE64.sign w ∧
      Wasm.IEEE64.fraction (w &&& mask) = Wasm.IEEE64.fraction w / 2 ^ 32 * 2 ^ 32 := by
  have h := mask_toNat w
  have hw := w.toNat_lt
  unfold Wasm.IEEE64.exponent Wasm.IEEE64.sign Wasm.IEEE64.fraction
  rw [h]
  refine ⟨by omega, ?_, by omega⟩
  simp only [decide_eq_decide]
  omega

/-- A truncated word: its magnitude has 21 significant bits from bit 32 of the scale, and its
value lies within `2 ^ -20` relative of the word, with the same sign. -/
theorem trunc_spec (w : UInt64) (hwf : Finite w) (he : 1 ≤ Wasm.IEEE64.exponent w) :
    Finite (w &&& mask) ∧ canon (w &&& mask) = w &&& mask ∧
      Wasm.IEEE64.exponent (w &&& mask) = Wasm.IEEE64.exponent w ∧
      Wasm.IEEE64.scaledMagnitude (w &&& mask) =
        (2 ^ 20 + Wasm.IEEE64.fraction w / 2 ^ 32) * 2 ^ (32 + (Wasm.IEEE64.exponent w - 1)) ∧
      |value (w &&& mask) - value w| ≤ |value w| / 2 ^ 20 ∧ |value (w &&& mask)| ≤ |value w| ∧
      0 ≤ value (w &&& mask) * value w := by
  obtain ⟨he', hs', hf'⟩ := trunc_fields w
  have hfin : Finite (w &&& mask) := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hwf ⊢
    rw [he']
    exact hwf
  have hcanon : canon (w &&& mask) = w &&& mask := by
    unfold canon
    have : Wasm.IEEE64.isNaN (w &&& mask) = false := by
      unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hfin
      unfold Wasm.IEEE64.isNaN
      simp only [bne_iff_ne, ne_eq] at hfin
      simp [hfin]
    rw [this]
    rfl
  have hne : (Wasm.IEEE64.exponent w == 0) = false := by simp; omega
  have hmw : Wasm.IEEE64.scaledMagnitude w =
      (2 ^ 52 + Wasm.IEEE64.fraction w) * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, hne, Bool.false_eq_true, ite_false]
  have hmz : Wasm.IEEE64.scaledMagnitude (w &&& mask) =
      (2 ^ 52 + Wasm.IEEE64.fraction w / 2 ^ 32 * 2 ^ 32) * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, he', hf', hne, Bool.false_eq_true, ite_false]
  have hmz' : Wasm.IEEE64.scaledMagnitude (w &&& mask) =
      (2 ^ 20 + Wasm.IEEE64.fraction w / 2 ^ 32) * 2 ^ (32 + (Wasm.IEEE64.exponent w - 1)) := by
    rw [hmz, pow_add]
    ring
  refine ⟨hfin, hcanon, he', hmz', ?_⟩
  -- Values through magnitudes and signs.
  have hf := Nat.mod_lt (Wasm.IEEE64.fraction w) (show 0 < 2 ^ 32 by positivity)
  have hdm := Nat.div_add_mod (Wasm.IEEE64.fraction w) (2 ^ 32)
  have hsv (v : UInt64) : value v = (if Wasm.IEEE64.sign v then -1 else 1) *
      ((Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074) := by
    rw [TrigSmall.value_of_scaled]
    unfold Wasm.IEEE64.scaledValue
    split <;> push_cast <;> ring
  set P : ℝ := (2 : ℝ) ^ (Wasm.IEEE64.exponent w - 1) / 2 ^ 1074 with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  set q := Wasm.IEEE64.fraction w / 2 ^ 32 * 2 ^ 32 with hq
  have hqf : (q : ℝ) ≤ Wasm.IEEE64.fraction w := by exact_mod_cast Nat.div_mul_le_self _ _
  have hqd : (Wasm.IEEE64.fraction w : ℝ) - q < 2 ^ 32 := by
    have h2 : q ≤ Wasm.IEEE64.fraction w := Nat.div_mul_le_self _ _
    have : Wasm.IEEE64.fraction w - q < 2 ^ 32 := by omega
    have h3 : ((Wasm.IEEE64.fraction w - q : Nat) : ℝ) < 2 ^ 32 := by exact_mod_cast this
    rw [Nat.cast_sub h2] at h3
    exact h3
  set Mz : ℝ := (2 ^ 52 + q) * P with hMz
  set Mw : ℝ := (2 ^ 52 + Wasm.IEEE64.fraction w) * P with hMw
  have hz : ((Wasm.IEEE64.scaledMagnitude (w &&& mask) : Nat) : ℝ) / 2 ^ 1074 = Mz := by
    rw [hmz, hMz, hP]; push_cast; ring
  have hw' : ((Wasm.IEEE64.scaledMagnitude w : Nat) : ℝ) / 2 ^ 1074 = Mw := by
    rw [hmw, hMw, hP]; push_cast; ring
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hMz0 : 0 ≤ Mz := mul_nonneg (by positivity) hP0.le
  have hdiff : Mw - Mz ≤ Mw / 2 ^ 20 := by
    have e1 : Mw - Mz = ((Wasm.IEEE64.fraction w : ℝ) - q) * P := by rw [hMw, hMz]; ring
    have e2 : (2 : ℝ) ^ 52 * P ≤ Mw := by
      rw [hMw]
      exact mul_le_mul_of_nonneg_right (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤
        Wasm.IEEE64.fraction w)]) hP0.le
    have e3 : ((Wasm.IEEE64.fraction w : ℝ) - q) * P ≤ 2 ^ 32 * P :=
      mul_le_mul_of_nonneg_right hqd.le hP0.le
    rw [e1, le_div_iff₀ (by positivity)]
    have : (2 : ℝ) ^ 32 * P * 2 ^ 20 = 2 ^ 52 * P := by ring
    nlinarith
  have hdiff0 : 0 ≤ Mw - Mz := by
    have e1 : Mw - Mz = ((Wasm.IEEE64.fraction w : ℝ) - q) * P := by rw [hMw, hMz]; ring
    rw [e1]
    exact mul_nonneg (by linarith) hP0.le
  rw [hsv (w &&& mask), hsv w, hs', hz, hw']
  cases Wasm.IEEE64.sign w
  · simp only [Bool.false_eq_true, ite_false, one_mul]
    rw [abs_of_nonneg hMz0, abs_of_nonneg (show 0 ≤ Mw by linarith),
      abs_of_nonpos (show Mz - Mw ≤ 0 by linarith)]
    exact ⟨by linarith, by linarith, mul_nonneg hMz0 (by linarith)⟩
  · simp only [ite_true]
    rw [show -1 * Mz - -1 * Mw = Mw - Mz by ring, abs_of_nonneg hdiff0,
      show -1 * Mz = -Mz by ring, show -1 * Mw = -Mw by ring, abs_neg, abs_neg,
      abs_of_nonneg hMz0, abs_of_nonneg (show 0 ≤ Mw by linarith)]
    exact ⟨hdiff, by linarith, by nlinarith⟩

/-- Two numbers of the same sign within a factor of two differ by at most the smaller. -/
theorem same_sign_diff (a b : ℝ) (hs : 0 ≤ a * b) (h1 : |b| ≤ 2 * |a|) (h2 : |a| ≤ 2 * |b|) :
    |a - b| ≤ |a| ∧ |a - b| ≤ |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb] at h1 h2 ⊢
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · have : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hb
    have hab : a * b = 0 := le_antisymm this hs
    rcases mul_eq_zero.mp hab with h | h
    · rw [h, abs_zero] at h1
      have : b = 0 := abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))
      rw [h, this]; simp
    · rw [h, abs_zero] at h2
      have : a = 0 := abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))
      rw [h, this]; simp
  · have : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hb
    have hab : a * b = 0 := le_antisymm this hs
    rcases mul_eq_zero.mp hab with h | h
    · rw [h, abs_zero] at h1
      have : b = 0 := abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))
      rw [h, this]; simp
    · rw [h, abs_zero] at h2
      have : a = 0 := abs_eq_zero.mp (le_antisymm (by linarith) (abs_nonneg _))
      rw [h, this]; simp
  · rw [abs_of_nonpos ha, abs_of_nonpos hb] at h1 h2 ⊢
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Sterbenz's lemma: two words of the same sign within a factor of two have an exact
difference. -/
theorem sterbenz (a b : UInt64) (ha : Finite a) (hb : Finite b) (hs : 0 ≤ value a * value b)
    (h1 : |value b| ≤ 2 * |value a|) (h2 : |value a| ≤ 2 * |value b|)
    (hea : Wasm.IEEE64.exponent a ≤ 2044) :
    Finite (Wasm.IEEE64.sub a b) ∧ value (Wasm.IEEE64.sub a b) = value a - value b := by
  obtain ⟨hda, hdb⟩ := same_sign_diff _ _ hs h1 h2
  have hga := TrigNearest.grid_bound a
  have hgb := TrigNearest.grid_bound b
  set m := min (Wasm.IEEE64.exponent a) (Wasm.IEEE64.exponent b) with hm
  have hdiv (v : UInt64) (h : m ≤ Wasm.IEEE64.exponent v) :
      (2 : Int) ^ (m - 1) ∣ Wasm.IEEE64.scaledValue v :=
    dvd_trans (pow_dvd_pow 2 (by omega)) (TrigNearest.grid_dvd v)
  refine TrigFloatTools.sub_exact a b ha hb (m - 1) (by omega) (hdiv a (min_le_left _ _))
    (hdiv b (min_le_right _ _)) ?_
  rcases min_choice (Wasm.IEEE64.exponent a) (Wasm.IEEE64.exponent b) with h | h
  · rw [hm, h]
    linarith
  · rw [hm, h]
    linarith

#print axioms high_mask
#print axioms trunc_spec
#print axioms sterbenz

end Verified.Examples.TanTrunc
