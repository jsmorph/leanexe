import Verified.Examples.Expm1FormsOne

/-!
The forms of fdlibm's `expm1` that compute `y1 = 1 - (e - x)`, a rounding of `exp r`, and then
`y1 2 ^ k - 1`: for `k ≤ -2` the subtraction of 1 rounds, and for `k ≥ 57` it returns
`y1 2 ^ k`, which `Expm1SubOne.sub_one_large` states.  For `k = 1024` the code multiplies by 2 and
by `2 ^ 1023` instead of by `2 ^ 1024`, which has no binary64 word.
-/

namespace Verified.Examples.Expm1FormsTwo
open CodeLib.IEEE64 LeanExe.ProofKit Expm1KernelInner Expm1FormBase Expm1FormsOne

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- `y1 = 1 - (e - x)`, a nearest word of `s1 = 1 - d` within `0.4901 u` of `exp r`. -/
theorem y1_spec (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) :
    let d := Wasm.IEEE64.sub (Expm1Words.e2 y c) y
    Finite d ∧
      Finite (Wasm.IEEE64.sub Expm1Words.one d) ∧
      F64NearestNonnegative.Nearest (1 - value d) (Wasm.IEEE64.sub Expm1Words.one d) ∧
      |value (Wasm.IEEE64.sub Expm1Words.one d) - (1 - value d)| ≤ 1 / 2 ^ 53 ∧
      |(1 - value d) - Real.exp r| ≤ 4901 / 10000 * u ∧
      |value d| < 4146 / 10000 ∧
      7070 / 10000 ≤ Real.exp r ∧ Real.exp r ≤ 14143 / 10000 := by
  intro d
  obtain ⟨he2f, -, hV, -, hlo, hhi⟩ := common y c hyf hcf hy hc r hr
  obtain ⟨hm, -, -⟩ := diff_spec y c hyf he2f r hV hlo hhi
  have hu : u = 1 / 2 ^ 53 := u_value
  have hs := F64NearestSum.sub_half_spacing (Expm1Words.e2 y c) y he2f hyf 1020
    (by rw [abs_sub_comm]; exact hm.trans (by norm_num)) (by norm_num)
  have hdf : Finite d := hs.1
  have hd : |value d - (value (Expm1Words.e2 y c) - value y)| ≤ 1 / 2 ^ 55 :=
    hs.2.trans (le_of_eq (by norm_num))
  have hdm : |value d| < 4146 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value d) (value (Expm1Words.e2 y c) - value y)
    rw [abs_sub_comm (value (Expm1Words.e2 y c))] at this
    have h1 : (1 : ℝ) / 2 ^ 55 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  have h1v : value Expm1Words.one = 1 := const_values.1
  have h1f : Finite Expm1Words.one := const_finite.1
  have hdb := abs_lt.mp hdm
  have hnear := F64NearestSum.sub_nearest Expm1Words.one d h1f hdf (by rw [h1v]; linarith)
    (by rw [h1v]; linarith)
  rw [h1v] at hnear
  have hhs := F64NearestSum.sub_half_spacing Expm1Words.one d h1f hdf 1022 (by
    rw [h1v, abs_lt]; constructor <;> norm_num <;> linarith) (by norm_num)
  rw [h1v] at hhs
  refine ⟨hdf, hhs.1, hnear, hhs.2.trans (le_of_eq (by norm_num)), ?_, hdm, hlo, hhi⟩
  have hsplit : (1 - value d) - Real.exp r =
      -(value d - (value (Expm1Words.e2 y c) - value y)) +
        ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) := by ring
  rw [hsplit]
  calc _ ≤ |-(value d - (value (Expm1Words.e2 y c) - value y))| +
        |(value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)| := abs_add_le _ _
    _ ≤ 1 / 2 ^ 55 + 2401 / 10000 * u := by rw [abs_neg]; exact add_le_add hd hV
    _ = 4901 / 10000 * u := by rw [hu]; norm_num

/-- Facts about the count `m` as a word. -/
theorem count_facts (m : UInt64) (h2 : 2 ≤ m.toNat) :
    (m == 0) = false ∧ (m == 1) = false := by
  constructor
  · simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h] at h2; simp at h2
  · simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h] at h2; simp at h2

/-- `k ≤ -2`: `y1 2 ^ k - 1`, rounded. -/
theorem form_neg (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm2 : 2 ≤ m.toNat) (hm56 : m.toNat ≤ 56) :
    F64SignedRounding.WithinSteps 1 (Real.exp r / 2 ^ m.toNat - 1)
      (Expm1Words.kernel y c true m) := by
  obtain ⟨hdf, hy1f, hnear, hy1, hs1, hdm, hlo, hhi⟩ := y1_spec y c hyf hcf hy hc r hr
  set d := Wasm.IEEE64.sub (Expm1Words.e2 y c) y
  set y1 := Wasm.IEEE64.sub Expm1Words.one d
  have hu : u = 1 / 2 ^ 53 := u_value
  obtain ⟨hm0, hm1⟩ := count_facts m hm2
  have hP := Expm1FormWords.twopk_neg m (by omega)
  have hk : Expm1Words.kernel y c true m =
      Wasm.IEEE64.sub (Wasm.IEEE64.mul y1 (Wasm.IEEE64.encodeFinite false (1023 - m.toNat) 0))
        Expm1Words.one := by
    simp [Expm1Words.kernel, hm0, hm1, hP, y1, d]
  rw [hk]
  -- `y1 ≥ 1/2`, so the product with `2 ^ -m` is exact.
  have hy1v : 1 / 2 ≤ value y1 := by
    have := abs_le.mp hy1
    have := abs_le.mp hs1
    have h1 : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h2 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  have hy1e : 1022 ≤ Wasm.IEEE64.exponent y1 :=
    F64Magnitude.exponent_ge_of_value y1 1022 (by norm_num) (by norm_num; exact hy1v)
  have hy1lt : Wasm.IEEE64.exponent y1 < 2047 := by
    have hf := hy1f
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    have : Wasm.IEEE64.exponent y1 < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
    omega
  have hPf := Expm1FormWords.power_finite (1023 - m.toNat) (by omega)
  rw [F64NearestScale.mul_comm_finite y1 _ hy1f hPf]
  have hmul := F64PowerScale.mul_power_finite (1023 - m.toNat) y1 (by omega) (by omega) hy1f
    (by omega) (by omega) (by omega)
  set v := Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false (1023 - m.toNat) 0) y1
  have hpow : (2 : ℝ) ^ (((1023 - m.toNat : Nat) : Int) - 1023) = 1 / 2 ^ m.toNat := by
    rw [show ((1023 - m.toNat : Nat) : Int) - 1023 = -(m.toNat : Int) by omega, zpow_neg,
      zpow_natCast, one_div]
  have hvv : value v = value y1 / 2 ^ m.toNat := by rw [hmul.2, hpow]; ring
  have h1v : value Expm1Words.one = 1 := const_values.1
  have h2m : (2 : ℝ) ^ m.toNat ≥ 4 := by
    calc (2 : ℝ) ^ m.toNat ≥ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hm2
      _ = 4 := by norm_num
  have hvle : value v ≤ 1 / 2 := by
    rw [hvv, div_le_iff₀ (by positivity)]
    have := abs_le.mp hy1
    have := abs_le.mp hs1
    have h1 : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h2 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 10 ^ 10 := by norm_num
    nlinarith
  have hneg : value v - value Expm1Words.one < 0 := by rw [h1v]; linarith
  have hnv := F64NearestSum.sub_nearest_neg v _ hmul.1 const_finite.1 hneg
    (by rw [h1v]; have : (0 : ℝ) ≤ value v := by rw [hvv]; positivity
        have : -(2 : ℝ) ^ 1023 < -1 := by norm_num
        linarith)
  apply (F64SignedRounding.within_negate 1 _ _).mp
  refine within_of_level _ _ _ 1022 (by norm_num) (by norm_num) ?_ ?_ hnv ?_
  · norm_num
    have : Real.exp r / 2 ^ m.toNat ≤ 14143 / 10000 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have : -(Real.exp r / 2 ^ m.toNat - 1) ≤ 1 := by
      have : 0 ≤ Real.exp r / 2 ^ m.toNat := by positivity
      linarith
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · rw [h1v, hvv]
    have hsplit : -(value y1 / 2 ^ m.toNat - 1) - -(Real.exp r / 2 ^ m.toNat - 1) =
        ((Real.exp r - (1 - value d)) - (value y1 - (1 - value d))) / 2 ^ m.toNat := by ring
    rw [hsplit, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m.toNat),
      div_lt_iff₀ (by positivity)]
    calc |(Real.exp r - (1 - value d)) - (value y1 - (1 - value d))| ≤
        |Real.exp r - (1 - value d)| + |value y1 - (1 - value d)| := abs_sub _ _
      _ ≤ 4901 / 10000 * u + 1 / 2 ^ 53 := by rw [abs_sub_comm]; exact add_le_add hs1 hy1
      _ < (2 : ℝ) ^ (1022 - 1) / 2 ^ 1074 * 4 := by rw [hu]; norm_num
      _ ≤ (2 : ℝ) ^ (1022 - 1) / 2 ^ 1074 * 2 ^ m.toNat := by gcongr

/-- `y1 < 2`, so its exponent field is at most 1023. -/
theorem y1_exponent (y1 : UInt64) (h : |value y1| < 2) : Wasm.IEEE64.exponent y1 < 1024 := by
  have hb : |value (F64ExponentBounds.boundary 1024)| = 2 := by
    rw [F64ExponentBounds.boundary, F64PositiveSpacing.boundary_value 1024 (by norm_num)
      (by norm_num), abs_of_pos (by positivity)]
    norm_num
  exact F64ExponentBounds.exponent_lt_of_magnitude_lt y1 1024 (by norm_num) (by rw [hb]; exact h)

theorem one_word : Expm1Words.one = 0x3FF0000000000000 := rfl

/-- `57 ≤ k ≤ 1023`: `y1 2 ^ k`, from which subtracting 1 changes nothing. -/
theorem form_large (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm57 : 57 ≤ m.toNat) (hm : m.toNat ≤ 1023) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ m.toNat * Real.exp r - 1)
      (Expm1Words.kernel y c false m) := by
  obtain ⟨hdf, hy1f, hnear, hy1, hs1, hdm, hlo, hhi⟩ := y1_spec y c hyf hcf hy hc r hr
  set d := Wasm.IEEE64.sub (Expm1Words.e2 y c) y
  set y1 := Wasm.IEEE64.sub Expm1Words.one d
  have hu : u = 1 / 2 ^ 53 := u_value
  obtain ⟨hm0, hm1⟩ := count_facts m (by omega)
  have hgt : (56 : UInt64) < m := UInt64.lt_iff_toNat_lt.mpr (by change 56 < m.toNat; omega)
  have hne : (m == 1024) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; rw [h] at hm; simp at hm
  have hP := Expm1FormWords.twopk_pos m hm
  have hk : Expm1Words.kernel y c false m =
      Wasm.IEEE64.sub (Wasm.IEEE64.mul y1 (Wasm.IEEE64.encodeFinite false (1023 + m.toNat) 0))
        Expm1Words.one := by
    simp [Expm1Words.kernel, hm0, hm1, hgt, hne, hP, y1, d]
  rw [hk]
  have hsmall1 : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  have hsmall2 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 10 ^ 10 := by norm_num
  have hy1b := abs_le.mp hy1
  have hs1b := abs_le.mp hs1
  have hy1e := y1_exponent y1 (by rw [abs_lt]; constructor <;> linarith)
  have hsc := F64NearestScale.scale_nearest _ y1 m.toNat (by omega) hm hnear
    (by have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 10 := by norm_num
        linarith) (by omega)
  obtain ⟨hvf, hvv, hvn⟩ := hsc
  set v := Wasm.IEEE64.mul y1 (Wasm.IEEE64.encodeFinite false (1023 + m.toNat) 0)
  have h2m : (2 : ℝ) ^ 57 ≤ 2 ^ m.toNat := pow_le_pow_right₀ (by norm_num) hm57
  have hvs : Wasm.IEEE64.sign v = false := (F64NearestNonnegative.nearest_finite _ _ hvn).2
  have hve : 1078 ≤ Wasm.IEEE64.exponent v := by
    apply F64Magnitude.exponent_ge_of_value v 1078 (by norm_num)
    rw [hvv]
    norm_num
    nlinarith
  rw [one_word, Expm1SubOne.sub_one_large v hvf hvs hve]
  refine within_of_level _ _ _ (1022 + m.toNat) (by omega) (by omega) ?_ ?_ hvn ?_
  · have h1 : ((2 : ℝ) ^ (1022 + m.toNat + 51) + 2 * 2 ^ (1022 + m.toNat - 1)) / 2 ^ 1074 =
        2 ^ m.toNat * (1 / 2 + 1 / 2 ^ 52) := by
      rw [show 1022 + m.toNat + 51 = 1073 + m.toNat by omega,
        show 1022 + m.toNat - 1 = 1021 + m.toNat by omega, pow_add, pow_add]
      field_simp
    rw [h1]
    nlinarith
  · have : (2 : ℝ) ^ m.toNat * Real.exp r - 1 ≤ 2 ^ 1023 * (14143 / 10000) := by
      have : (2 : ℝ) ^ m.toNat ≤ 2 ^ 1023 := pow_le_pow_right₀ (by norm_num) hm
      nlinarith [Real.exp_pos r]
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · have h1 : (2 : ℝ) ^ (1022 + m.toNat - 1) / 2 ^ 1074 = 2 ^ m.toNat * (1 / 2 ^ 53) := by
      rw [show 1022 + m.toNat - 1 = 1021 + m.toNat by omega, pow_add]
      field_simp
    rw [h1]
    have hsplit : (2 : ℝ) ^ m.toNat * (1 - value d) - (2 ^ m.toNat * Real.exp r - 1) =
        2 ^ m.toNat * ((1 - value d) - Real.exp r) + 1 := by ring
    rw [hsplit]
    calc |(2 : ℝ) ^ m.toNat * ((1 - value d) - Real.exp r) + 1| ≤
        2 ^ m.toNat * (4901 / 10000 * u) + 1 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m.toNat), abs_one]
          gcongr
      _ < 2 ^ m.toNat * (1 / 2 ^ 53) := by
          rw [hu]
          have : (2 : ℝ) ^ 57 * (1 / 2 ^ 53) * (5099 / 10000) ≤
              2 ^ m.toNat * (1 / 2 ^ 53) * (5099 / 10000) := by gcongr
          nlinarith

/-- `k = 1024`: `y1 2 · 2 ^ 1023`, from which subtracting 1 changes nothing.  The hypothesis on
`exp r` holds below the overflow threshold of the code. -/
theorem form_top (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm : m.toNat = 1024)
    (hexp : Real.exp r ≤ 1 - 1 / 2 ^ 40) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ 1024 * Real.exp r - 1)
      (Expm1Words.kernel y c false m) := by
  obtain ⟨hdf, hy1f, hnear, hy1, hs1, hdm, hlo, hhi⟩ := y1_spec y c hyf hcf hy hc r hr
  set d := Wasm.IEEE64.sub (Expm1Words.e2 y c) y
  set y1 := Wasm.IEEE64.sub Expm1Words.one d
  have hu : u = 1 / 2 ^ 53 := u_value
  have hm' : m = 1024 := UInt64.toNat_inj.mp (by rw [hm]; rfl)
  subst hm'
  have hk : Expm1Words.kernel y c false 1024 =
      Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.mul y1 Expm1Words.two)
        (Wasm.IEEE64.encodeFinite false 2046 0)) Expm1Words.one := by
    rw [← Expm1FormWords.maxPower_eq]
    simp [Expm1Words.kernel, y1, d]
  rw [hk]
  have hsmall1 : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  have hy1b := abs_le.mp hy1
  have hs1b := abs_le.mp hs1
  -- `y1 < 1`: the word below 1 is nearer to `s1` than 1 is.
  have hs1lt : 1 - value d < 1 - 1 / 2 ^ 53 := by
    have h1 : 4901 / 10000 * u ≤ 4901 / 10000 / 2 ^ 53 := by rw [hu]; norm_num
    have h2 : (1 : ℝ) - 1 / 2 ^ 40 + 4901 / 10000 / 2 ^ 53 < 1 - 1 / 2 ^ 53 := by norm_num
    linarith
  have hy1lt : value y1 < 1 := by
    by_contra hge
    have hw : (0x3FEFFFFFFFFFFFFF : UInt64).toNat < F64NearestNonnegative.limit := by decide
    have hwv : value (0x3FEFFFFFFFFFFFFF : UInt64) = 1 - 1 / 2 ^ 53 := by
      have h : Wasm.IEEE64.scaledValue (0x3FEFFFFFFFFFFFFF : UInt64) = 2 ^ 1074 - 2 ^ 1021 := by
        decide +kernel
      rw [value, h]; push_cast; field_simp; ring
    have := hnear.2 _ hw
    rw [hwv, abs_of_pos (by linarith : (0 : ℝ) < 1 - 1 / 2 ^ 53 - (1 - value d)),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ value y1 - (1 - value d))] at this
    linarith
  have hy1pos : 0 < value y1 := by linarith
  have hy1e := y1_exponent y1 (by rw [abs_lt]; constructor <;> linarith)
  -- `v1 = 2 y1`.
  have hsc1 := F64NearestScale.scale_nearest _ y1 1 le_rfl (by norm_num) hnear
    (by have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 10 := by norm_num
        linarith) (by omega)
  rw [show (1023 + 1 : Nat) = 1024 from rfl, ← Expm1FormWords.two_eq] at hsc1
  obtain ⟨hv1f, hv1v, hv1n⟩ := hsc1
  set v1 := Wasm.IEEE64.mul y1 Expm1Words.two
  have hv1e := y1_exponent v1 (by rw [hv1v, abs_lt]; constructor <;> norm_num <;> linarith)
  -- `v2 = 2 ^ 1023 v1`.
  have hsc2 := F64NearestScale.scale_nearest _ v1 1023 (by norm_num) le_rfl hv1n
    (by have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 10 := by norm_num
        linarith) (by omega)
  rw [show (1023 + 1023 : Nat) = 2046 from rfl] at hsc2
  obtain ⟨hv2f, hv2v, hv2n⟩ := hsc2
  set v2 := Wasm.IEEE64.mul v1 (Wasm.IEEE64.encodeFinite false 2046 0)
  have hv2s : Wasm.IEEE64.sign v2 = false := (F64NearestNonnegative.nearest_finite _ _ hv2n).2
  have hv2e : 1078 ≤ Wasm.IEEE64.exponent v2 := by
    apply F64Magnitude.exponent_ge_of_value v2 1078 (by norm_num)
    rw [hv2v, hv1v]
    norm_num
    nlinarith
  rw [one_word, Expm1SubOne.sub_one_large v2 hv2f hv2s hv2e]
  refine within_of_level _ _ _ 2046 (by norm_num) le_rfl ?_ ?_ hv2n ?_
  · norm_num
    nlinarith
  · have : (2 : ℝ) ^ 1024 * Real.exp r - 1 ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 40) := by
      nlinarith [Real.exp_pos r]
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · have hsplit : (2 : ℝ) ^ 1023 * (2 ^ 1 * (1 - value d)) - (2 ^ 1024 * Real.exp r - 1) =
        2 ^ 1024 * ((1 - value d) - Real.exp r) + 1 := by ring
    rw [hsplit]
    calc |(2 : ℝ) ^ 1024 * ((1 - value d) - Real.exp r) + 1| ≤
        2 ^ 1024 * (4901 / 10000 * u) + 1 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1024), abs_one]
          gcongr
      _ < (2 : ℝ) ^ (2046 - 1) / 2 ^ 1074 := by rw [hu]; norm_num

#print axioms y1_spec
#print axioms form_neg
#print axioms form_large
#print axioms form_top

end Verified.Examples.Expm1FormsTwo
