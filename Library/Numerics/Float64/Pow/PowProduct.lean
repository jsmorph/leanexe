import Library.Numerics.Float64.Pow.PowLogSum
import Library.Numerics.Float64.Pow.PowExpPaths

/-!
The product `y log x` of `Pow.powMain` as `ehi + elo`.  `yhi` and `lhi` keep the top 26
significant bits of `y` and of the high word of `log x`, by clearing the low 27 bits of their
words, so `ehi = yhi lhi` is exact and `yhi`, `lhi` lie within `2 ^ -25` of `y` and `hi` in
relative terms.  `elo = (y - yhi) lhi + y ((hi - lhi) + lo)` carries a few roundings of
quantities below `2 ^ -24 |y hi|`, so `ehi + elo` lies within `2 ^ -74 |y (hi + lo)|` of
`y (hi + lo)`, and `|elo| ≤ 17 · 2 ^ -28 |ehi|`.
-/

namespace Library.Numerics.Float64.Pow.PowProduct
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The word with the low 27 bits of `w` cleared. -/
def mask (w : UInt64) : UInt64 := w &&& 0xFFFFFFFFF8000000

theorem mask_toNat (w : UInt64) : (mask w).toNat = w.toNat / 2 ^ 27 * 2 ^ 27 := by
  have hT := w.toNat_lt
  rw [mask, UInt64.toNat_and, show (0xFFFFFFFFF8000000 : UInt64).toNat =
    (2 ^ 37 - 1) * 2 ^ 27 by decide]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hj : 27 ≤ j
  · have he : j - 27 + 27 = j := by omega
    rw [he]
    by_cases hj2 : j < 64
    · simp [hj, show j - 27 < 37 by omega]
    · have hlt : w.toNat < 2 ^ j :=
        lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hlt]
      simp
  · simp [hj]

/-- A normal word and its masked word: the same sign and exponent field, a significand of at
most 26 bits, and a relative difference below `2 ^ -25`. -/
theorem mask_state (w : UInt64) (hw : Finite w) (he : 1 ≤ Wasm.IEEE64.exponent w) :
    Finite (mask w) ∧ Wasm.IEEE64.sign (mask w) = Wasm.IEEE64.sign w ∧
      (∃ M : Nat, M < 2 ^ 26 ∧ Wasm.IEEE64.scaledMagnitude (mask w) =
        M * 2 ^ (Wasm.IEEE64.exponent w - 1 + 27)) ∧
      |value w - value (mask w)| ≤ |value w| / 2 ^ 25 ∧
      |value (mask w)| ≤ |value w| := by
  have hm := mask_toNat w
  have hT := w.toNat_lt
  set e := Wasm.IEEE64.exponent w
  set g := Wasm.IEEE64.fraction w
  have hfin : e < 2047 := by
    have h := hw
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : e < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hg : g < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have he' : Wasm.IEEE64.exponent (mask w) = e := by
    simp only [Wasm.IEEE64.exponent, hm]
    simp only [e, Wasm.IEEE64.exponent]
    simp only [Nat.reducePow] at hT ⊢
    omega
  have hg' : Wasm.IEEE64.fraction (mask w) = g / 2 ^ 27 * 2 ^ 27 := by
    simp only [Wasm.IEEE64.fraction, hm]
    simp only [g, Wasm.IEEE64.fraction]
    simp only [Nat.reducePow] at hT ⊢
    omega
  have hs' : Wasm.IEEE64.sign (mask w) = Wasm.IEEE64.sign w := by
    simp only [Wasm.IEEE64.sign, hm]
    simp only [Nat.reducePow] at hT ⊢
    congr 1
    apply propext
    omega
  have hmf : Finite (mask w) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, he', bne_iff_ne, ne_eq]
    omega
  have hmag : Wasm.IEEE64.scaledMagnitude w = (2 ^ 52 + g) * 2 ^ (e - 1) := by
    have he0 : (Wasm.IEEE64.exponent w == 0) = false := by
      rw [beq_eq_false_iff_ne]
      change e ≠ 0
      omega
    unfold Wasm.IEEE64.scaledMagnitude
    simp only [he0, Bool.false_eq_true, ite_false]
    all_goals rfl
  have hmag' : Wasm.IEEE64.scaledMagnitude (mask w) = (2 ^ 52 + g / 2 ^ 27 * 2 ^ 27) * 2 ^ (e - 1) := by
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, he', hg', show e ≠ 0 by omega, ite_false]
  refine ⟨hmf, hs', ⟨(2 ^ 52 + g) / 2 ^ 27, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Nat.reducePow] at hg ⊢
    omega
  · rw [hmag', pow_add]
    have : 2 ^ 52 + g / 2 ^ 27 * 2 ^ 27 = (2 ^ 52 + g) / 2 ^ 27 * 2 ^ 27 := by
      simp only [Nat.reducePow] at hg ⊢
      omega
    rw [this]
    ring
  · -- the difference in scaled units
    have hd : Wasm.IEEE64.scaledMagnitude w - Wasm.IEEE64.scaledMagnitude (mask w) =
        g % 2 ^ 27 * 2 ^ (e - 1) := by
      rw [hmag, hmag']
      have : 2 ^ 52 + g = 2 ^ 52 + g / 2 ^ 27 * 2 ^ 27 + g % 2 ^ 27 := by
        have := Nat.div_add_mod g (2 ^ 27)
        omega
      rw [this, add_mul, Nat.add_sub_cancel_left]
    have hle : Wasm.IEEE64.scaledMagnitude (mask w) ≤ Wasm.IEEE64.scaledMagnitude w := by
      rw [hmag, hmag']
      apply Nat.mul_le_mul_right
      have := Nat.div_mul_le_self g (2 ^ 27)
      omega
    have habs : ∀ v : UInt64, |value v| = (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by
      intro v
      rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← Int.cast_abs,
        Int.abs_eq_natAbs, natAbs_scaledValue]
      push_cast
      rfl
    have hsame : value w - value (mask w) = (if Wasm.IEEE64.sign w then -1 else 1) *
        ((Wasm.IEEE64.scaledMagnitude w : ℝ) - Wasm.IEEE64.scaledMagnitude (mask w)) / 2 ^ 1074 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs']
      split_ifs <;> push_cast <;> ring
    have hdiff : |value w - value (mask w)| =
        ((g % 2 ^ 27 * 2 ^ (e - 1) : Nat) : ℝ) / 2 ^ 1074 := by
      rw [hsame, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
      have h1 : |(if Wasm.IEEE64.sign w then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> simp
      rw [h1, one_mul, ← hd, Nat.cast_sub hle, abs_of_nonneg]
      have : (Wasm.IEEE64.scaledMagnitude (mask w) : ℝ) ≤ Wasm.IEEE64.scaledMagnitude w := by
        exact_mod_cast hle
      linarith
    rw [hdiff, habs, hmag, div_right_comm]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 : g % 2 ^ 27 < 2 ^ 27 := Nat.mod_lt _ (by positivity)
    have h2 : ((g % 2 ^ 27 * 2 ^ (e - 1) : Nat) : ℝ) ≤ (2 ^ 27 * 2 ^ (e - 1) : ℝ) := by
      have : g % 2 ^ 27 * 2 ^ (e - 1) ≤ 2 ^ 27 * 2 ^ (e - 1) := Nat.mul_le_mul_right _ h1.le
      exact_mod_cast this
    have h3 : (2 ^ 27 * 2 ^ (e - 1) : ℝ) ≤ ((2 ^ 52 + g) * 2 ^ (e - 1) : Nat) / 2 ^ 25 := by
      push_cast
      rw [le_div_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ (g : ℝ) * 2 ^ (e - 1) := by positivity
      nlinarith [show (0 : ℝ) < 2 ^ (e - 1) by positivity]
    exact h2.trans h3
  · have habs : ∀ v : UInt64, |value v| = (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by
      intro v
      rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← Int.cast_abs,
        Int.abs_eq_natAbs, natAbs_scaledValue]
      push_cast
      rfl
    rw [habs, habs]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : Wasm.IEEE64.scaledMagnitude (mask w) ≤ Wasm.IEEE64.scaledMagnitude w := by
      rw [hmag, hmag']
      apply Nat.mul_le_mul_right
      have := Nat.div_mul_le_self g (2 ^ 27)
      omega
    exact_mod_cast this

theorem exponent_of_abs (w : UInt64) (e : Nat) (he1 : 1 ≤ e)
    (h : (2 : ℝ) ^ ((e : Int) - 1023) ≤ |value w|) : e ≤ Wasm.IEEE64.exponent w := by
  by_contra hn
  have := F64Magnitude.magnitude_lt w e ((e : Int) - 1023) he1 (by ring) (by omega)
  linarith

theorem exponent_le_of_abs (w : UInt64) (e : Nat) (he1 : 1 ≤ e) (he2 : e < 2048)
    (h : |value w| < (2 : ℝ) ^ ((e : Int) - 1023)) : Wasm.IEEE64.exponent w < e := by
  by_contra hn
  have := F64Magnitude.magnitude_ge w e ((e : Int) - 1023) he1 he2 (by ring) (by omega)
  linarith

/-- `u t ≤ c` for `0 ≤ u ≤ 1` and `0 ≤ t ≤ c`. -/
theorem scale_le (u t c : ℝ) (hu1 : u ≤ 1) (ht0 : 0 ≤ t) (ht : t ≤ c) :
    u * t ≤ c := by
  have h := mul_le_mul_of_nonneg_right hu1 ht0
  linarith

/-- The arithmetic of `product_error` on the values of its words: `yv`, `Y`, and `Tv` for `y`,
`hi`, and `lo`, `Yh` and `Lh` for the masked words, `YL`, `D`, and `LL` for `y - yhi`,
`hi - lhi`, and `D + lo`, `P1` and `P2` for the two products, and `S` for their sum. -/
theorem product_real (yv Y Tv Yh Lh YL D LL P1 P2 S μ : ℝ)
    (hμ1 : μ ≤ 1 / 2 ^ 1000) (hy1 : 1 / 2 ^ 65 ≤ |yv|) (hY1 : 1 / 2 ^ 54 ≤ |Y|)
    (hdy : |yv - Yh| ≤ |yv| / 2 ^ 25) (hdl : |Y - Lh| ≤ |Y| / 2 ^ 25)
    (hmlb : |Lh| ≤ |Y|) (hT : |Tv| ≤ |Y| / 2 ^ 50)
    (hyle : |YL - (yv - Yh)| ≤ 1 / 2 ^ 53 * |yv - Yh|)
    (hde : |D - (Y - Lh)| ≤ 1 / 2 ^ 53 * |Y - Lh|)
    (hlle : |LL - (D + Tv)| ≤ 1 / 2 ^ 53 * |D + Tv|)
    (hp1e : |P1 - YL * Lh| ≤ 1 / 2 ^ 53 * |YL * Lh| + μ)
    (hp2e : |P2 - yv * LL| ≤ 1 / 2 ^ 53 * |yv * LL| + μ)
    (heloe : |S - (P1 + P2)| ≤ 1 / 2 ^ 53 * |P1 + P2|) :
    |Yh * Lh + S - yv * (Y + Tv)| ≤ |yv * (Y + Tv)| / 2 ^ 74 ∧
      |S| ≤ 17 / 2 ^ 28 * |Yh * Lh| := by
  set A := |yv| with hAdef
  set B := |Y| with hBdef
  set Dy := yv - Yh with hDydef
  set Dl := Y - Lh with hDldef
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hAB : 1 / 2 ^ 119 ≤ A * B := by
    have := mul_le_mul hy1 hY1 (by positivity) hA0
    calc
      (1 : ℝ) / 2 ^ 119 = 1 / 2 ^ 65 * (1 / 2 ^ 54) := by norm_num
      _ ≤ A * B := this
  have hdb : |D| ≤ (1 + 1 / 2 ^ 53) * (B / 2 ^ 25) := by
    have h1 := abs_sub_abs_le_abs_sub D Dl
    have h2 : 1 / 2 ^ 53 * |Dl| ≤ 1 / 2 ^ 53 * (B / 2 ^ 25) :=
      mul_le_mul_of_nonneg_left hdl (by positivity)
    linarith
  have hllo : |LL - (Dl + Tv)| ≤ 1 / 2 ^ 53 * (3 * (B / 2 ^ 25)) := by
    have h1 := abs_add_le D Tv
    have h2 : |LL - (Dl + Tv)| ≤ |LL - (D + Tv)| + |D - Dl| := by
      have := abs_add_le (LL - (D + Tv)) (D - Dl)
      rw [show LL - (D + Tv) + (D - Dl) = LL - (Dl + Tv) by ring] at this
      exact this
    have h3 : 1 / 2 ^ 53 * |D + Tv| ≤
        1 / 2 ^ 53 * ((1 + 1 / 2 ^ 53) * (B / 2 ^ 25) + B / 2 ^ 50) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : 1 / 2 ^ 53 * |Dl| ≤ 1 / 2 ^ 53 * (B / 2 ^ 25) :=
      mul_le_mul_of_nonneg_left hdl (by positivity)
    linarith
  have hllb : |LL| ≤ B / 2 ^ 24 := by
    have h1 := abs_sub_abs_le_abs_sub LL (Dl + Tv)
    have h2 := abs_add_le Dl Tv
    linarith
  have hylo : |YL| ≤ (1 + 1 / 2 ^ 53) * (A / 2 ^ 25) := by
    have h1 := abs_sub_abs_le_abs_sub YL Dy
    have h2 : 1 / 2 ^ 53 * |Dy| ≤ 1 / 2 ^ 53 * (A / 2 ^ 25) :=
      mul_le_mul_of_nonneg_left hdy (by positivity)
    linarith
  have hp1b : |YL * Lh| ≤ (1 + 1 / 2 ^ 53) * (A / 2 ^ 25) * B := by
    rw [abs_mul]
    exact mul_le_mul hylo hmlb (abs_nonneg _) (by positivity)
  have hp2b : |yv * LL| ≤ A * (B / 2 ^ 24) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hllb hA0
  have hμ' : μ ≤ A * B / 2 ^ 800 := by
    have : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 119 / 2 ^ 800 := by norm_num
    have h2 : 1 / 2 ^ 119 / 2 ^ 800 ≤ A * B / 2 ^ 800 :=
      div_le_div_of_nonneg_right hAB (by positivity)
    linarith
  have hp12 : |P1 + P2| ≤ A * B / 2 ^ 23 := by
    have h1 := abs_sub_abs_le_abs_sub P1 (YL * Lh)
    have h2 := abs_sub_abs_le_abs_sub P2 (yv * LL)
    have h3 := abs_add_le P1 P2
    have h4 : 1 / 2 ^ 53 * |YL * Lh| ≤ 1 / 2 ^ 53 * ((1 + 1 / 2 ^ 53) * (A / 2 ^ 25) * B) :=
      mul_le_mul_of_nonneg_left hp1b (by positivity)
    have h5 : 1 / 2 ^ 53 * |yv * LL| ≤ 1 / 2 ^ 53 * (A * (B / 2 ^ 24)) :=
      mul_le_mul_of_nonneg_left hp2b (by positivity)
    linarith
  have hexact : Dy * Lh + yv * (Dl + Tv) = yv * (Y + Tv) - Yh * Lh := by
    rw [hDydef, hDldef]
    ring
  have hμ2 : 2 * μ ≤ A * B / 2 ^ 80 := by
    have : (2 : ℝ) * (1 / 2 ^ 1000) ≤ 1 / 2 ^ 119 / 2 ^ 80 := by norm_num
    have h2 : 1 / 2 ^ 119 / 2 ^ 80 ≤ A * B / 2 ^ 80 :=
      div_le_div_of_nonneg_right hAB (by positivity)
    linarith
  have herr : |S - (Dy * Lh + yv * (Dl + Tv))| ≤ 3 * (A * B) / 2 ^ 76 + 2 * μ := by
    have e1 : |YL * Lh - Dy * Lh| ≤ 1 / 2 ^ 53 * (A / 2 ^ 25) * B := by
      rw [← sub_mul, abs_mul]
      have : |YL - Dy| ≤ 1 / 2 ^ 53 * (A / 2 ^ 25) :=
        hyle.trans (mul_le_mul_of_nonneg_left hdy (by positivity))
      exact mul_le_mul this hmlb (abs_nonneg _) (by positivity)
    have e2 : |yv * LL - yv * (Dl + Tv)| ≤ A * (1 / 2 ^ 53 * (3 * (B / 2 ^ 25))) := by
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hllo hA0
    have e3 : 1 / 2 ^ 53 * |YL * Lh| ≤ 1 / 2 ^ 53 * ((1 + 1 / 2 ^ 53) * (A / 2 ^ 25) * B) :=
      mul_le_mul_of_nonneg_left hp1b (by positivity)
    have e4 : 1 / 2 ^ 53 * |yv * LL| ≤ 1 / 2 ^ 53 * (A * (B / 2 ^ 24)) :=
      mul_le_mul_of_nonneg_left hp2b (by positivity)
    have e5 : 1 / 2 ^ 53 * |P1 + P2| ≤ 1 / 2 ^ 53 * (A * B / 2 ^ 23) :=
      mul_le_mul_of_nonneg_left hp12 (by positivity)
    have hsplit : |S - (Dy * Lh + yv * (Dl + Tv))| ≤
        |S - (P1 + P2)| + |P1 - YL * Lh| + |YL * Lh - Dy * Lh| +
        |P2 - yv * LL| + |yv * LL - yv * (Dl + Tv)| := by
      have h1 := abs_add_le (S - (P1 + P2)) (P1 - YL * Lh)
      have h2 := abs_add_le (S - (P1 + P2) + (P1 - YL * Lh)) (YL * Lh - Dy * Lh)
      have h3 := abs_add_le (S - (P1 + P2) + (P1 - YL * Lh) + (YL * Lh - Dy * Lh))
        (P2 - yv * LL)
      have h4 := abs_add_le (S - (P1 + P2) + (P1 - YL * Lh) + (YL * Lh - Dy * Lh) +
        (P2 - yv * LL)) (yv * LL - yv * (Dl + Tv))
      rw [show S - (P1 + P2) + (P1 - YL * Lh) + (YL * Lh - Dy * Lh) + (P2 - yv * LL) +
        (yv * LL - yv * (Dl + Tv)) = S - (Dy * Lh + yv * (Dl + Tv)) by ring] at h4
      linarith
    have hAB0 := mul_nonneg hA0 hB0
    linarith
  have hYT : A * B * (1 - 1 / 2 ^ 50) ≤ |yv * (Y + Tv)| := by
    rw [abs_mul]
    have : B * (1 - 1 / 2 ^ 50) ≤ |Y + Tv| := by
      have := abs_sub_abs_le_abs_sub Y (-Tv)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    calc
      A * B * (1 - 1 / 2 ^ 50) = A * (B * (1 - 1 / 2 ^ 50)) := by ring
      _ ≤ A * |Y + Tv| := mul_le_mul_of_nonneg_left this hA0
  have hAB0 := mul_nonneg hA0 hB0
  constructor
  · have hid : Yh * Lh + S - yv * (Y + Tv) = S - (Dy * Lh + yv * (Dl + Tv)) := by
      rw [hexact]
      ring
    rw [hid]
    linarith
  · rw [abs_mul]
    have hYh : A * (1 - 1 / 2 ^ 25) ≤ |Yh| := by
      have := abs_sub_abs_le_abs_sub yv Yh
      linarith
    have hLh : B * (1 - 1 / 2 ^ 25) ≤ |Lh| := by
      have := abs_sub_abs_le_abs_sub Y Lh
      linarith
    have hprod : A * B * ((1 - 1 / 2 ^ 25) * (1 - 1 / 2 ^ 25)) ≤ |Yh| * |Lh| := by
      calc
        A * B * ((1 - 1 / 2 ^ 25) * (1 - 1 / 2 ^ 25)) =
            (A * (1 - 1 / 2 ^ 25)) * (B * (1 - 1 / 2 ^ 25)) := by ring
        _ ≤ |Yh| * |Lh| := mul_le_mul hYh hLh (by positivity) (abs_nonneg _)
    have hex : |Dy * Lh + yv * (Dl + Tv)| ≤ A * B * (2 / 2 ^ 25 + 1 / 2 ^ 50) := by
      have h1 := abs_add_le (Dy * Lh) (yv * (Dl + Tv))
      have h2 : |Dy * Lh| ≤ A / 2 ^ 25 * B := by
        rw [abs_mul]
        exact mul_le_mul hdy hmlb (abs_nonneg _) (by positivity)
      have h3 : |yv * (Dl + Tv)| ≤ A * (B / 2 ^ 25 + B / 2 ^ 50) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hdl hT)) hA0
      linarith
    have := abs_sub_abs_le_abs_sub S (Dy * Lh + yv * (Dl + Tv))
    linarith

/-- `y log x` as `ehi + elo`. -/
theorem product_error (y hiF loF : Float) (hyf : Finite y.toBits) (hhf : Finite hiF.toBits)
    (hlf : Finite loF.toBits) (hy1 : 1 / 2 ^ 65 ≤ |value y.toBits|)
    (hy2 : |value y.toBits| < 2 ^ 63) (hY1 : 1 / 2 ^ 54 ≤ |value hiF.toBits|)
    (hY2 : |value hiF.toBits| ≤ 800)
    (hT : |value loF.toBits| ≤ |value hiF.toBits| / 2 ^ 50) :
    let yhi := Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000)
    let lhi := Float.ofBits (hiF.toBits &&& 0xFFFFFFFFF8000000)
    let ehi := yhi * lhi
    let elo := (y - yhi) * lhi + y * (hiF - lhi + loF)
    Finite ehi.toBits ∧ Finite elo.toBits ∧
      |value ehi.toBits + value elo.toBits - value y.toBits * (value hiF.toBits + value loF.toBits)| ≤
        |value y.toBits * (value hiF.toBits + value loF.toBits)| / 2 ^ 74 ∧
      |value elo.toBits| ≤ 17 / 2 ^ 28 * |value ehi.toBits| := by
  intro yhi lhi ehi elo
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hμ0 : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  have hμ1 : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon]
  -- the exponent fields
  have hey : 958 ≤ Wasm.IEEE64.exponent y.toBits := exponent_of_abs _ 958 (by norm_num)
    (by norm_num at hy1 ⊢; exact hy1)
  have hey2 : Wasm.IEEE64.exponent y.toBits < 1087 := exponent_le_of_abs _ 1087 (by norm_num)
    (by norm_num) (by norm_num at hy2 ⊢; linarith)
  have hel : 969 ≤ Wasm.IEEE64.exponent hiF.toBits := exponent_of_abs _ 969 (by norm_num)
    (by norm_num at hY1 ⊢; exact hY1)
  have hel2 : Wasm.IEEE64.exponent hiF.toBits < 1033 := exponent_le_of_abs _ 1033
    (by norm_num) (by norm_num) (by norm_num; linarith)
  obtain ⟨hmyf, -, ⟨My, hMy, hmy⟩, hdy, hmyb⟩ := mask_state _ hyf (by omega)
  obtain ⟨hmlf, -, ⟨Ml, hMl, hml⟩, hdl, hmlb⟩ := mask_state _ hhf (by omega)
  have hyb : yhi.toBits = mask y.toBits := PowExpPaths.ofBits_finite _ hmyf
  have hlb : lhi.toBits = mask hiF.toBits := PowExpPaths.ofBits_finite _ hmlf
  -- `ehi` is exact
  obtain ⟨hef, hev, -, -⟩ := F64ExactProduct.mul_exact_scaled (mask y.toBits) (mask hiF.toBits)
    hmyf hmlf My Ml _ _ hmy hml
    (by calc My * Ml < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul'' hMy hMl
          _ = 2 ^ 52 := by norm_num
          _ < 2 ^ 53 := by norm_num) (by omega) (by omega)
  have hehi : ehi.toBits = Wasm.IEEE64.mul (mask y.toBits) (mask hiF.toBits) := by
    show (yhi * lhi).toBits = _
    rw [F64Bits.toBits_mul, hyb, hlb]
  have helo : elo.toBits = Wasm.IEEE64.add
      (Wasm.IEEE64.mul (Wasm.IEEE64.sub y.toBits (mask y.toBits)) (mask hiF.toBits))
      (Wasm.IEEE64.mul y.toBits
        (Wasm.IEEE64.add (Wasm.IEEE64.sub hiF.toBits (mask hiF.toBits)) loF.toBits)) := by
    show ((y - yhi) * lhi + y * (hiF - lhi + loF)).toBits = _
    rw [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_mul, F64Bits.toBits_sub,
      F64Bits.toBits_add, F64Bits.toBits_sub, hyb, hlb]
  rw [hehi, helo]
  have hu0 : (0 : ℝ) ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hu1 : unitRoundoff64 ≤ 1 := by norm_num [unitRoundoff64]
  have hlo800 : |value loF.toBits| ≤ 800 := by
    have : |value hiF.toBits| / 2 ^ 50 ≤ 800 := by
      have := div_le_self (abs_nonneg (value hiF.toBits)) (by norm_num : (1 : ℝ) ≤ 2 ^ 50)
      linarith
    linarith
  -- crude magnitudes, for the overflow conditions
  have hyv := abs_nonneg (value y.toBits)
  have hYv := abs_nonneg (value hiF.toBits)
  have hc1 : |value y.toBits - value (mask y.toBits)| < (2 : ℝ) ^ 1023 := by
    have := abs_sub (value y.toBits) (value (mask y.toBits))
    linarith [show (2 : ℝ) ^ 63 + 2 ^ 63 < 2 ^ 1023 by norm_num]
  obtain ⟨hylf, hyle⟩ := F64AddBounds.sub_real_relative _ _ hyf hmyf hc1
  have hc2 : |value hiF.toBits - value (mask hiF.toBits)| < (2 : ℝ) ^ 1023 := by
    have := abs_sub (value hiF.toBits) (value (mask hiF.toBits))
    linarith [show (800 : ℝ) + 800 < 2 ^ 1023 by norm_num]
  obtain ⟨hdf, hde⟩ := F64AddBounds.sub_real_relative _ _ hhf hmlf hc2
  have hdcrude : |value (Wasm.IEEE64.sub hiF.toBits (mask hiF.toBits))| ≤ 4000 := by
    have h1 := abs_sub_abs_le_abs_sub (value (Wasm.IEEE64.sub hiF.toBits (mask hiF.toBits)))
      (value hiF.toBits - value (mask hiF.toBits))
    have h2 := abs_sub (value hiF.toBits) (value (mask hiF.toBits))
    have h3 := scale_le _ _ 1600 hu1
      (abs_nonneg (value hiF.toBits - value (mask hiF.toBits))) (by linarith)
    linarith
  have hc3 : |value (Wasm.IEEE64.sub hiF.toBits (mask hiF.toBits)) + value loF.toBits| <
      (2 : ℝ) ^ 1023 := by
    have := abs_add_le (value (Wasm.IEEE64.sub hiF.toBits (mask hiF.toBits))) (value loF.toBits)
    linarith [show (4000 : ℝ) + 800 < 2 ^ 1023 by norm_num]
  obtain ⟨hllf, hlle⟩ := F64AddBounds.add_real_relative _ _ hdf hlf hc3
  set d := Wasm.IEEE64.sub hiF.toBits (mask hiF.toBits)
  set ylo := Wasm.IEEE64.sub y.toBits (mask y.toBits)
  set llo := Wasm.IEEE64.add d loF.toBits
  have hylcrude : |value ylo| ≤ 2 ^ 65 := by
    have h1 := abs_sub_abs_le_abs_sub (value ylo) (value y.toBits - value (mask y.toBits))
    have h2 := abs_sub (value y.toBits) (value (mask y.toBits))
    have h3 := scale_le _ _ (2 ^ 64) hu1
      (abs_nonneg (value y.toBits - value (mask y.toBits)))
      (by linarith [show (2 : ℝ) ^ 63 + 2 ^ 63 = 2 ^ 64 by norm_num])
    linarith [show (2 : ℝ) ^ 63 + 2 ^ 63 + 2 ^ 64 ≤ 2 ^ 65 by norm_num]
  have hllcrude : |value llo| ≤ 10000 := by
    have h1 := abs_sub_abs_le_abs_sub (value llo) (value d + value loF.toBits)
    have h2 := abs_add_le (value d) (value loF.toBits)
    have h4 := scale_le _ _ 4800 hu1 (abs_nonneg (value d + value loF.toBits))
      (by linarith)
    linarith
  obtain ⟨hp1f, hp1e⟩ := F64MulBounds.mul_real_mixed ylo (mask hiF.toBits) hylf hmlf (by
    rw [abs_mul]
    have := mul_le_mul hylcrude (hmlb.trans hY2) (abs_nonneg _) (by positivity)
    linarith [show (2 : ℝ) ^ 65 * 800 < 2 ^ 1022 by norm_num])
  obtain ⟨hp2f, hp2e⟩ := F64MulBounds.mul_real_mixed y.toBits llo hyf hllf (by
    rw [abs_mul]
    have := mul_le_mul hy2.le hllcrude (abs_nonneg _) (by positivity)
    linarith [show (2 : ℝ) ^ 63 * 10000 < 2 ^ 1022 by norm_num])
  set p1 := Wasm.IEEE64.mul ylo (mask hiF.toBits)
  set p2 := Wasm.IEEE64.mul y.toBits llo
  have hp12crude : |value p1 + value p2| < (2 : ℝ) ^ 1023 := by
    have h1 := abs_add_le (value p1) (value p2)
    have h2 := abs_sub_abs_le_abs_sub (value p1) (value ylo * value (mask hiF.toBits))
    have h3 := abs_sub_abs_le_abs_sub (value p2) (value y.toBits * value llo)
    have h4 : |value ylo * value (mask hiF.toBits)| ≤ 2 ^ 65 * 800 := by
      rw [abs_mul]
      exact mul_le_mul hylcrude (hmlb.trans hY2) (abs_nonneg _) (by positivity)
    have h5 : |value y.toBits * value llo| ≤ 2 ^ 63 * 10000 := by
      rw [abs_mul]
      exact mul_le_mul hy2.le hllcrude (abs_nonneg _) (by positivity)
    have h6 := scale_le _ _ _ hu1 (abs_nonneg (value ylo * value (mask hiF.toBits))) h4
    have h7 := scale_le _ _ _ hu1 (abs_nonneg (value y.toBits * value llo)) h5
    have hμ' : multiplicationUnderflowEpsilon ≤ 1 := by
      linarith [show (1 : ℝ) / 2 ^ 1000 ≤ 1 by norm_num]
    linarith [show (2 : ℝ) * (2 ^ 65 * 800) + 2 * (2 ^ 63 * 10000) + 2 < 2 ^ 1023 by norm_num]
  obtain ⟨helof, heloe⟩ := F64AddBounds.add_real_relative p1 p2 hp1f hp2f hp12crude
  rw [hu] at hyle hde hlle hp1e hp2e heloe
  obtain ⟨r1, r2⟩ := product_real (value y.toBits) (value hiF.toBits) (value loF.toBits)
    (value (mask y.toBits)) (value (mask hiF.toBits)) (value ylo) (value d) (value llo)
    (value p1) (value p2) (value (Wasm.IEEE64.add p1 p2)) multiplicationUnderflowEpsilon
    hμ1 hy1 hY1 hdy hdl hmlb hT hyle hde hlle hp1e hp2e heloe
  refine ⟨hef, helof, ?_, ?_⟩
  · rw [hev]
    exact r1
  · rw [hev]
    exact r2

#print axioms mask_toNat
#print axioms mask_state
#print axioms exponent_of_abs
#print axioms exponent_le_of_abs
#print axioms scale_le
#print axioms product_real
#print axioms product_error

end Library.Numerics.Float64.Pow.PowProduct
