import Verified.Examples.Expm1FormsTwo

/-!
The forms of fdlibm's `expm1` for `2 ≤ k ≤ 56`, which subtract `2 ^ -k` before the last rounding
and then scale by `2 ^ k` exactly.  For `k < 20` the code rounds `(1 - 2 ^ -k) - (e - x)`, and for
`20 ≤ k ≤ 56` it rounds `(x - (e + 2 ^ -k)) + 1`.
-/

namespace Verified.Examples.Expm1FormsMid
open CodeLib.IEEE64 LeanExe.ProofKit Expm1KernelInner Expm1FormBase Expm1FormsOne Expm1FormsTwo

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

/-- `2 ≤ k < 20`: `((1 - 2 ^ -k) - (e - x)) 2 ^ k`. -/
theorem form_mid_low (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm2 : 2 ≤ m.toNat) (hm20 : m.toNat < 20) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ m.toNat * Real.exp r - 1)
      (Expm1Words.kernel y c false m) := by
  obtain ⟨hdf, -, -, -, hs1, hdm, hlo, hhi⟩ := y1_spec y c hyf hcf hy hc r hr
  set d := Wasm.IEEE64.sub (Expm1Words.e2 y c) y
  have hu : u = 1 / 2 ^ 53 := u_value
  obtain ⟨hm0, hm1⟩ := count_facts m hm2
  have hle56 : ¬ (56 : UInt64) < m := by
    rw [UInt64.lt_iff_toNat_lt]; change ¬ 56 < m.toNat; omega
  have hlt20 : m < 20 := UInt64.lt_iff_toNat_lt.mpr (by change m.toNat < 20; omega)
  have hP := Expm1FormWords.twopk_pos m (by omega)
  have hk : Expm1Words.kernel y c false m =
      Wasm.IEEE64.mul (Wasm.IEEE64.sub (Expm1Words.oneMinus m) d)
        (Wasm.IEEE64.encodeFinite false (1023 + m.toNat) 0) := by
    simp [Expm1Words.kernel, hm0, hm1, hle56, hlt20, hP, d]
  rw [hk]
  obtain ⟨htf, htv⟩ := Expm1FormWords.oneMinus_spec m hm2 hm20
  have h2m : (4 : ℝ) ≤ 2 ^ m.toNat := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m.toNat := pow_le_pow_right₀ (by norm_num) hm2
  have hinv : 1 / (2 : ℝ) ^ m.toNat ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinv0 : 0 < 1 / (2 : ℝ) ^ m.toNat := by positivity
  have hdb := abs_lt.mp hdm
  have hsmall : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  have hs1b := abs_le.mp hs1
  -- `b` rounds `s_b = (1 - 2 ^ -k) - d`, between 0.45 and 1.42.
  have hsb : 45 / 100 ≤ value (Expm1Words.oneMinus m) - value d := by rw [htv]; linarith
  have hnb := F64NearestSum.sub_nearest _ d htf hdf (by linarith) (by rw [htv]; linarith)
  have hg2 : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
  have hbs := F64NearestSum.sub_half_spacing _ d htf hdf 1022 (by
    rw [htv, hg2, abs_lt]; constructor <;> linarith) (by norm_num)
  set b := Wasm.IEEE64.sub (Expm1Words.oneMinus m) d
  have hgh : (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = 1 / 2 ^ 53 := by norm_num
  have hbm : |value b| < 2 := by
    have := abs_le.mp hbs.2
    rw [htv, hgh] at this
    have h53 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 10 ^ 10 := by norm_num
    rw [abs_lt]; constructor <;> linarith
  have hbe := y1_exponent b hbm
  have hsc := F64NearestScale.scale_nearest _ b m.toNat (by omega) (by omega) hnb
    (by have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 10 := by norm_num
        linarith) (lt_of_lt_of_le (Nat.add_lt_add_right hbe m.toNat) (by omega))
  refine within_of_level _ _ _ (1021 + m.toNat) (by omega) (by omega) ?_ ?_ hsc.2.2 ?_
  · have h1 : ((2 : ℝ) ^ (1021 + m.toNat + 51) + 2 * 2 ^ (1021 + m.toNat - 1)) / 2 ^ 1074 =
        2 ^ m.toNat * (1 / 4 + 1 / 2 ^ 53) := by
      rw [show 1021 + m.toNat + 51 = 1072 + m.toNat by omega,
        show 1021 + m.toNat - 1 = 1020 + m.toNat by omega, pow_add, pow_add]
      field_simp
      norm_num
    rw [h1]
    have : (2 : ℝ) ^ m.toNat * (1 / 2 ^ m.toNat) = 1 := by field_simp
    nlinarith
  · have : (2 : ℝ) ^ m.toNat * Real.exp r - 1 ≤ 2 ^ 19 * (14143 / 10000) := by
      have : (2 : ℝ) ^ m.toNat ≤ 2 ^ 19 := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [Real.exp_pos r]
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · have h1 : (2 : ℝ) ^ (1021 + m.toNat - 1) / 2 ^ 1074 = 2 ^ m.toNat * (1 / 2 ^ 54) := by
      rw [show 1021 + m.toNat - 1 = 1020 + m.toNat by omega, pow_add]
      field_simp
    rw [h1, htv]
    have hsplit : (2 : ℝ) ^ m.toNat * (1 - 1 / 2 ^ m.toNat - value d) -
        (2 ^ m.toNat * Real.exp r - 1) = 2 ^ m.toNat * ((1 - value d) - Real.exp r) := by
      field_simp
      ring
    rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m.toNat)]
    have hp : (0 : ℝ) < 2 ^ m.toNat := by positivity
    calc (2 : ℝ) ^ m.toNat * |(1 - value d) - Real.exp r| ≤ 2 ^ m.toNat * (4901 / 10000 * u) :=
          mul_le_mul_of_nonneg_left hs1 hp.le
      _ < 2 ^ m.toNat * (1 / 2 ^ 54) := by
          apply mul_lt_mul_of_pos_left _ hp
          rw [hu]; norm_num

/-- `20 ≤ k ≤ 56`: `((x - (e + 2 ^ -k)) + 1) 2 ^ k`. -/
theorem form_mid_high (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm20 : 20 ≤ m.toNat) (hm56 : m.toNat ≤ 56) :
    F64SignedRounding.WithinSteps 1 ((2 : ℝ) ^ m.toNat * Real.exp r - 1)
      (Expm1Words.kernel y c false m) := by
  obtain ⟨he2f, he2m, hV, -, hlo, hhi⟩ := common y c hyf hcf hy hc r hr
  obtain ⟨hm, -, -⟩ := diff_spec y c hyf he2f r hV hlo hhi
  have hu : u = 1 / 2 ^ 53 := u_value
  obtain ⟨hm0, hm1⟩ := count_facts m (by omega)
  have hle56 : ¬ (56 : UInt64) < m := by
    rw [UInt64.lt_iff_toNat_lt]; change ¬ 56 < m.toNat; omega
  have hge20 : ¬ m < 20 := by
    rw [UInt64.lt_iff_toNat_lt]; change ¬ m.toNat < 20; omega
  have hP := Expm1FormWords.twopk_pos m (by omega)
  have hT := Expm1FormWords.powerNeg_eq m (by omega)
  set E := Expm1Words.e2 y c
  set tw := Wasm.IEEE64.encodeFinite false (1023 - m.toNat) 0
  have hk : Expm1Words.kernel y c false m =
      Wasm.IEEE64.mul (Wasm.IEEE64.add (Wasm.IEEE64.sub y (Wasm.IEEE64.add E tw))
        Expm1Words.one) (Wasm.IEEE64.encodeFinite false (1023 + m.toNat) 0) := by
    simp [Expm1Words.kernel, hm0, hm1, hle56, hge20, hP, hT, E, tw]
  rw [hk]
  have htwf := Expm1FormWords.power_finite (1023 - m.toNat) (by omega)
  have htwv : value tw = 1 / 2 ^ m.toNat := by
    rw [Expm1FormWords.power_value _ (by omega) (by omega),
      show 1023 - m.toNat + 51 = 1074 - m.toNat by omega]
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
    congr 1; omega
  have h2m : (2 : ℝ) ^ 20 ≤ 2 ^ m.toNat := pow_le_pow_right₀ (by norm_num) hm20
  have hinv : 1 / (2 : ℝ) ^ m.toNat ≤ 1 / 2 ^ 20 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hinv0 : 0 < 1 / (2 : ℝ) ^ m.toNat := by positivity
  have he2b := abs_le.mp he2m
  have hmb := abs_lt.mp hm
  have hsmall : 2401 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  -- `a = e + 2 ^ -k`, below `1/8`.
  have hg8 : (2 : ℝ) ^ (53 + 1018) / 2 ^ 1074 = 1 / 8 := by norm_num
  have has := F64NearestSum.add_half_spacing E tw he2f htwf 1018 (by
    rw [htwv, hg8, abs_lt]; constructor <;> linarith) (by norm_num)
  set a := Wasm.IEEE64.add E tw
  have hae : |value a - (value E + 1 / 2 ^ m.toNat)| ≤ 1 / 2 ^ 57 := by
    rw [← htwv]; exact has.2.trans (le_of_eq (by norm_num))
  have haeb := abs_le.mp hae
  have h57 : (1 : ℝ) / 2 ^ 57 ≤ 1 / 10 ^ 10 := by norm_num
  -- `bb = x - a`, below `1/2`.
  have hg05 : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = 1 / 2 := by norm_num
  have hbs := F64NearestSum.sub_half_spacing y a hyf has.1 1020 (by
    rw [hg05, abs_lt]; constructor <;> linarith) (by norm_num)
  set bb := Wasm.IEEE64.sub y a
  have hbe : |value bb - (value y - value a)| ≤ 1 / 2 ^ 55 :=
    hbs.2.trans (le_of_eq (by norm_num))
  have hbeb := abs_le.mp hbe
  have h55 : (1 : ℝ) / 2 ^ 55 ≤ 1 / 10 ^ 10 := by norm_num
  -- `dd = bb + 1`, between 0.5 and 1.5.
  have h1v : value Expm1Words.one = 1 := const_values.1
  have hnd := F64NearestSum.add_nearest bb Expm1Words.one hbs.1 const_finite.1
    (by rw [h1v]; linarith) (by rw [h1v]; linarith)
  rw [h1v] at hnd
  have hg2 : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
  have hds := F64NearestSum.add_half_spacing bb Expm1Words.one hbs.1 const_finite.1 1022 (by
    rw [h1v, hg2, abs_lt]; constructor <;> linarith) (by norm_num)
  set dd := Wasm.IEEE64.add bb Expm1Words.one
  have hgh : (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = 1 / 2 ^ 53 := by norm_num
  have hddm : |value dd| < 2 := by
    have := abs_le.mp hds.2
    rw [h1v, hgh] at this
    have h53 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 10 ^ 10 := by norm_num
    rw [abs_lt]; constructor <;> linarith
  have hdde := y1_exponent dd hddm
  have hsc := F64NearestScale.scale_nearest _ dd m.toNat (by omega) (by omega) hnd
    (by have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 10 := by norm_num
        linarith) (lt_of_lt_of_le (Nat.add_lt_add_right hdde m.toNat) (by omega))
  refine within_of_level _ _ _ (1022 + m.toNat) (by omega) (by omega) ?_ ?_ hsc.2.2 ?_
  · have h1 : ((2 : ℝ) ^ (1022 + m.toNat + 51) + 2 * 2 ^ (1022 + m.toNat - 1)) / 2 ^ 1074 =
        2 ^ m.toNat * (1 / 2 + 1 / 2 ^ 52) := by
      rw [show 1022 + m.toNat + 51 = 1073 + m.toNat by omega,
        show 1022 + m.toNat - 1 = 1021 + m.toNat by omega, pow_add, pow_add]
      field_simp
    rw [h1]
    have : (2 : ℝ) ^ m.toNat * (1 / 2 ^ m.toNat) = 1 := by field_simp
    nlinarith
  · have : (2 : ℝ) ^ m.toNat * Real.exp r - 1 ≤ 2 ^ 56 * (14143 / 10000) := by
      have : (2 : ℝ) ^ m.toNat ≤ 2 ^ 56 := pow_le_pow_right₀ (by norm_num) hm56
      nlinarith [Real.exp_pos r]
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · have h1 : (2 : ℝ) ^ (1022 + m.toNat - 1) / 2 ^ 1074 = 2 ^ m.toNat * (1 / 2 ^ 53) := by
      rw [show 1022 + m.toNat - 1 = 1021 + m.toNat by omega, pow_add]
      field_simp
    rw [h1]
    have hp : (0 : ℝ) < 2 ^ m.toNat := by positivity
    have hsplit : (2 : ℝ) ^ m.toNat * (value bb + 1) - (2 ^ m.toNat * Real.exp r - 1) =
        2 ^ m.toNat * ((value bb - (value y - value a)) -
          (value a - (value E + 1 / 2 ^ m.toNat)) +
          ((value y - value E) - (Real.exp r - 1))) := by
      field_simp
      ring
    rw [hsplit, abs_mul, abs_of_pos hp]
    apply mul_lt_mul_of_pos_left _ hp
    calc _ ≤ |value bb - (value y - value a)| + |value a - (value E + 1 / 2 ^ m.toNat)| +
          |(value y - value E) - (Real.exp r - 1)| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 / 2 ^ 55 + 1 / 2 ^ 57 + 2401 / 10000 * u := add_le_add (add_le_add hbe hae) hV
      _ < 1 / 2 ^ 53 := by rw [hu]; norm_num

#print axioms form_mid_low
#print axioms form_mid_high

end Verified.Examples.Expm1FormsMid
