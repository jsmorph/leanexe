import Verified.Examples.Expm1FormsMid
import LeanExe.ProofKit.F64RelativeStep

/-!
The scaling forms of fdlibm's `expm1` with the error of the exact value before the last rounding
exported.  For negative results the kernel returns `-w` for a positive word `w`, the rounding of a
positive `S` with `abs(w - S) ≤ u S` and `abs(w - S) ≤ u/2`; for positive results it returns a
word within `u S` of a positive `S`.  Each theorem bounds `S` against the exact result.
-/

namespace Verified.Examples.Expm1NearForms
open CodeLib.IEEE64 LeanExe.ProofKit Expm1KernelInner Expm1FormBase Expm1FormsOne Expm1FormsTwo

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- A negative difference in `(-1, 0)`, rounded and negated. -/
theorem final_neg (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hneg : value a - value b < 0) (hgt : -1 < value a - value b) :
    Wasm.IEEE64.sub a b = Wasm.IEEE64.negate (Wasm.IEEE64.negate (Wasm.IEEE64.sub a b)) ∧
      Finite (Wasm.IEEE64.negate (Wasm.IEEE64.sub a b)) ∧
      |value (Wasm.IEEE64.negate (Wasm.IEEE64.sub a b)) - (value b - value a)| ≤
        u * (value b - value a) ∧
      |value (Wasm.IEEE64.negate (Wasm.IEEE64.sub a b)) - (value b - value a)| ≤ u / 2 := by
  have hu : u = 1 / 2 ^ 53 := u_value
  have hab : |value a - value b| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hr := F64AddBounds.sub_real_relative a b ha hb (hab.trans (by norm_num))
  have hs := F64NearestSum.sub_half_spacing a b ha hb 1021
    (hab.trans_le (by norm_num)) (by norm_num)
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value _ hr.1
  refine ⟨(F64RelativeStep.negate_negate _).symm, hnf, ?_, ?_⟩
  · rw [hnv, show -value (Wasm.IEEE64.sub a b) - (value b - value a) =
      -(value (Wasm.IEEE64.sub a b) - (value a - value b)) by ring, abs_neg]
    refine hr.2.trans (le_of_eq ?_)
    rw [abs_of_neg hneg]; ring
  · rw [hnv, show -value (Wasm.IEEE64.sub a b) - (value b - value a) =
      -(value (Wasm.IEEE64.sub a b) - (value a - value b)) by ring, abs_neg]
    refine hs.2.trans (le_of_eq ?_)
    rw [hu]; norm_num

/-- `k = -1`: `(x - e)/2 - 1/2 = -w`, with `S` within `0.2451 u` of `1 - exp r / 2`. -/
theorem neg_one_near (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) :
    ∃ w : UInt64, ∃ S : ℝ, Expm1Words.kernel y c true 1 = Wasm.IEEE64.negate w ∧ Finite w ∧
      |value w - S| ≤ u * S ∧ |value w - S| ≤ u / 2 ∧
      |S - (1 - Real.exp r / 2)| ≤ 2451 / 10000 * u := by
  obtain ⟨he2f, -, hV, -, hlo, hhi⟩ := common y c hyf hcf hy hc r hr
  obtain ⟨hm, hdf, hd⟩ := diff_spec y c hyf he2f r hV hlo hhi
  have hu : u = 1 / 2 ^ 53 := u_value
  have hη : η = 1 / 2 ^ 1075 := eta_value
  set d := Wasm.IEEE64.sub y (Expm1Words.e2 y c)
  obtain ⟨hhf, hh⟩ := hfx_spec d hdf
  set h := Expm1Words.hfx d
  have hk : Expm1Words.kernel y c true 1 = Wasm.IEEE64.sub h Expm1Words.half := by
    simp [Expm1Words.kernel, h, d, Expm1Words.hfx]
  have hhalf : value Expm1Words.half = 1 / 2 := const_values.2.1
  have hfh : Finite Expm1Words.half := const_finite.2.1
  have hdm : |value d| < 4146 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value d) (value y - value (Expm1Words.e2 y c))
    have h1 : (1 : ℝ) / 2 ^ 55 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  have hhb := abs_le.mp hh
  have h2η : 2 * η ≤ 1 / 10 ^ 10 := by rw [hη]; norm_num
  have hdb := abs_lt.mp hdm
  obtain ⟨heq, hwf, hw1, hw2⟩ := final_neg h _ hhf hfh (by rw [hhalf]; linarith)
    (by rw [hhalf]; linarith)
  refine ⟨_, value Expm1Words.half - value h, by rw [hk]; exact heq, hwf, hw1, hw2, ?_⟩
  rw [hhalf]
  have hsplit : (1 / 2 - value h) - (1 - Real.exp r / 2) =
      -((value h - value d / 2) + (value d - (value y - value (Expm1Words.e2 y c))) / 2 +
        ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) / 2) := by ring
  rw [hsplit, abs_neg]
  calc _ ≤ |value h - value d / 2| + |(value d - (value y - value (Expm1Words.e2 y c))) / 2| +
        |((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) / 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * η + 1 / 2 ^ 55 / 2 + 2401 / 10000 * u / 2 := by
        rw [abs_div, abs_div, abs_two]
        gcongr
    _ ≤ 2451 / 10000 * u := by rw [hu, hη]; norm_num

/-- `k ≤ -2`: `y1 2 ^ k - 1 = -w`, with `S` within `0.3726 u` of `1 - exp r / 2 ^ m`. -/
theorem neg_k_near (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm2 : 2 ≤ m.toNat) (hm56 : m.toNat ≤ 56) :
    ∃ w : UInt64, ∃ S : ℝ, Expm1Words.kernel y c true m = Wasm.IEEE64.negate w ∧ Finite w ∧
      |value w - S| ≤ u * S ∧ |value w - S| ≤ u / 2 ∧
      |S - (1 - Real.exp r / 2 ^ m.toNat)| ≤ 3726 / 10000 * u := by
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
  rw [F64NearestScale.mul_comm_finite y1 _ hy1f hPf] at hk
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
  have hv0 : 0 < value v := by
    rw [hvv]
    have : (0 : ℝ) < value y1 := by linarith
    positivity
  obtain ⟨heq, hwf, hw1, hw2⟩ := final_neg v _ hmul.1 const_finite.1
    (by rw [h1v]; linarith) (by rw [h1v]; linarith)
  refine ⟨_, value Expm1Words.one - value v, by rw [hk]; exact heq, hwf, hw1, hw2, ?_⟩
  rw [h1v, hvv]
  have hsplit : (1 - value y1 / 2 ^ m.toNat) - (1 - Real.exp r / 2 ^ m.toNat) =
      ((Real.exp r - (1 - value d)) - (value y1 - (1 - value d))) / 2 ^ m.toNat := by ring
  rw [hsplit, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m.toNat),
    div_le_iff₀ (by positivity)]
  calc |(Real.exp r - (1 - value d)) - (value y1 - (1 - value d))| ≤
      |Real.exp r - (1 - value d)| + |value y1 - (1 - value d)| := abs_sub _ _
    _ ≤ 4901 / 10000 * u + 1 / 2 ^ 53 := by rw [abs_sub_comm]; exact add_le_add hs1 hy1
    _ ≤ 3726 / 10000 * u * 4 := by rw [hu]; norm_num
    _ ≤ 3726 / 10000 * u * 2 ^ m.toNat := by
        apply mul_le_mul_of_nonneg_left h2m
        rw [hu]; norm_num

/-- `3 ≤ k < 20`: the result is within `u S` of `S`, and `S` within `0.85 u` of the result
relative to it. -/
theorem mid_low_near (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm3 : 3 ≤ m.toNat) (hm20 : m.toNat < 20) :
    ∃ S : ℝ, Finite (Expm1Words.kernel y c false m) ∧ 0 < S ∧
      |value (Expm1Words.kernel y c false m) - S| ≤ u * S ∧
      |S - ((2 : ℝ) ^ m.toNat * Real.exp r - 1)| ≤
        85 / 100 * u * ((2 : ℝ) ^ m.toNat * Real.exp r - 1) := by
  obtain ⟨hdf, -, -, -, hs1, hdm, hlo, hhi⟩ := y1_spec y c hyf hcf hy hc r hr
  set d := Wasm.IEEE64.sub (Expm1Words.e2 y c) y
  have hu : u = 1 / 2 ^ 53 := u_value
  obtain ⟨hm0, hm1⟩ := count_facts m (by omega)
  have hle56 : ¬ (56 : UInt64) < m := by
    rw [UInt64.lt_iff_toNat_lt]; change ¬ 56 < m.toNat; omega
  have hlt20 : m < 20 := UInt64.lt_iff_toNat_lt.mpr (by change m.toNat < 20; omega)
  have hP := Expm1FormWords.twopk_pos m (by omega)
  have hk : Expm1Words.kernel y c false m =
      Wasm.IEEE64.mul (Wasm.IEEE64.sub (Expm1Words.oneMinus m) d)
        (Wasm.IEEE64.encodeFinite false (1023 + m.toNat) 0) := by
    simp [Expm1Words.kernel, hm0, hm1, hle56, hlt20, hP, d]
  rw [hk]
  obtain ⟨htf, htv⟩ := Expm1FormWords.oneMinus_spec m (by omega) hm20
  have h2m : (8 : ℝ) ≤ 2 ^ m.toNat := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m.toNat := pow_le_pow_right₀ (by norm_num) hm3
  have hinv : 1 / (2 : ℝ) ^ m.toNat ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hinv0 : 0 < 1 / (2 : ℝ) ^ m.toNat := by positivity
  have hdb := abs_lt.mp hdm
  have hsmall : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  have hs1b := abs_le.mp hs1
  have hsb : 45 / 100 ≤ value (Expm1Words.oneMinus m) - value d := by rw [htv]; linarith
  have hnb := F64NearestSum.sub_nearest _ d htf hdf (by linarith) (by rw [htv]; linarith)
  have hbr := F64AddBounds.sub_real_relative _ d htf hdf (by
    rw [htv, abs_lt]; constructor <;> linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  set b := Wasm.IEEE64.sub (Expm1Words.oneMinus m) d
  have hg2 : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
  have hbs := F64NearestSum.sub_half_spacing _ d htf hdf 1022 (by
    rw [htv, hg2, abs_lt]; constructor <;> linarith) (by norm_num)
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
  set sb := value (Expm1Words.oneMinus m) - value d
  have hp : (0 : ℝ) < 2 ^ m.toNat := by positivity
  refine ⟨2 ^ m.toNat * sb, hsc.1, by positivity, ?_, ?_⟩
  · rw [hsc.2.1, ← mul_sub, abs_mul, abs_of_pos hp, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ hp.le
    have := hbr.2
    rwa [abs_of_pos (by linarith : (0 : ℝ) < sb)] at this
  · have hsplit : (2 : ℝ) ^ m.toNat * sb - (2 ^ m.toNat * Real.exp r - 1) =
        2 ^ m.toNat * ((1 - value d) - Real.exp r) := by
      rw [show sb = 1 - 1 / 2 ^ m.toNat - value d by simp only [sb, htv]]
      field_simp; ring
    rw [hsplit, abs_mul, abs_of_pos hp]
    have h1 : (2 : ℝ) ^ m.toNat * |(1 - value d) - Real.exp r| ≤
        2 ^ m.toNat * (4901 / 10000 * u) := mul_le_mul_of_nonneg_left hs1 hp.le
    have h2 : (2 : ℝ) ^ m.toNat * (4901 / 10000) ≤
        85 / 100 * ((2 : ℝ) ^ m.toNat * Real.exp r - 1) := by nlinarith
    have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
    calc (2 : ℝ) ^ m.toNat * |(1 - value d) - Real.exp r| ≤
        2 ^ m.toNat * (4901 / 10000 * u) := h1
      _ = (2 ^ m.toNat * (4901 / 10000)) * u := by ring
      _ ≤ (85 / 100 * ((2 : ℝ) ^ m.toNat * Real.exp r - 1)) * u :=
          mul_le_mul_of_nonneg_right h2 hu0
      _ = _ := by ring

/-- `20 ≤ k ≤ 56`: as `mid_low_near`. -/
theorem mid_high_near (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm20 : 20 ≤ m.toNat) (hm56 : m.toNat ≤ 56) :
    ∃ S : ℝ, Finite (Expm1Words.kernel y c false m) ∧ 0 < S ∧
      |value (Expm1Words.kernel y c false m) - S| ≤ u * S ∧
      |S - ((2 : ℝ) ^ m.toNat * Real.exp r - 1)| ≤
        85 / 100 * u * ((2 : ℝ) ^ m.toNat * Real.exp r - 1) := by
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
  have hg8 : (2 : ℝ) ^ (53 + 1018) / 2 ^ 1074 = 1 / 8 := by norm_num
  have has := F64NearestSum.add_half_spacing E tw he2f htwf 1018 (by
    rw [htwv, hg8, abs_lt]; constructor <;> linarith) (by norm_num)
  set a := Wasm.IEEE64.add E tw
  have hae : |value a - (value E + 1 / 2 ^ m.toNat)| ≤ 1 / 2 ^ 57 := by
    rw [← htwv]; exact has.2.trans (le_of_eq (by norm_num))
  have haeb := abs_le.mp hae
  have h57 : (1 : ℝ) / 2 ^ 57 ≤ 1 / 10 ^ 10 := by norm_num
  have hg05 : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = 1 / 2 := by norm_num
  have hbs := F64NearestSum.sub_half_spacing y a hyf has.1 1020 (by
    rw [hg05, abs_lt]; constructor <;> linarith) (by norm_num)
  set bb := Wasm.IEEE64.sub y a
  have hbe : |value bb - (value y - value a)| ≤ 1 / 2 ^ 55 :=
    hbs.2.trans (le_of_eq (by norm_num))
  have hbeb := abs_le.mp hbe
  have h55 : (1 : ℝ) / 2 ^ 55 ≤ 1 / 10 ^ 10 := by norm_num
  have h1v : value Expm1Words.one = 1 := const_values.1
  have hnd := F64NearestSum.add_nearest bb Expm1Words.one hbs.1 const_finite.1
    (by rw [h1v]; linarith) (by rw [h1v]; linarith)
  rw [h1v] at hnd
  have hdr := F64AddBounds.add_real_relative bb Expm1Words.one hbs.1 const_finite.1 (by
    rw [h1v, abs_lt]; constructor <;> linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  rw [h1v] at hdr
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
  have hp : (0 : ℝ) < 2 ^ m.toNat := by positivity
  refine ⟨2 ^ m.toNat * (value bb + 1), hsc.1, by nlinarith, ?_, ?_⟩
  · rw [hsc.2.1, ← mul_sub, abs_mul, abs_of_pos hp, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ hp.le
    have := hdr.2
    rwa [abs_of_pos (by linarith : (0 : ℝ) < value bb + 1)] at this
  · have hsplit : (2 : ℝ) ^ m.toNat * (value bb + 1) - (2 ^ m.toNat * Real.exp r - 1) =
        2 ^ m.toNat * ((value bb - (value y - value a)) -
          (value a - (value E + 1 / 2 ^ m.toNat)) +
          ((value y - value E) - (Real.exp r - 1))) := by
      field_simp
      ring
    rw [hsplit, abs_mul, abs_of_pos hp]
    have h1 : |(value bb - (value y - value a)) - (value a - (value E + 1 / 2 ^ m.toNat)) +
        ((value y - value E) - (Real.exp r - 1))| ≤ 5526 / 10000 * u := by
      calc _ ≤ |value bb - (value y - value a)| + |value a - (value E + 1 / 2 ^ m.toNat)| +
            |(value y - value E) - (Real.exp r - 1)| :=
            (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ 1 / 2 ^ 55 + 1 / 2 ^ 57 + 2401 / 10000 * u := add_le_add (add_le_add hbe hae) hV
        _ ≤ 5526 / 10000 * u := by rw [hu]; norm_num
    have h2 : (2 : ℝ) ^ m.toNat * (5526 / 10000) ≤
        85 / 100 * ((2 : ℝ) ^ m.toNat * Real.exp r - 1) := by nlinarith
    have hu0 : (0 : ℝ) ≤ u := by rw [hu]; positivity
    calc (2 : ℝ) ^ m.toNat * |_| ≤ 2 ^ m.toNat * (5526 / 10000 * u) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = (2 ^ m.toNat * (5526 / 10000)) * u := by ring
      _ ≤ (85 / 100 * ((2 : ℝ) ^ m.toNat * Real.exp r - 1)) * u :=
          mul_le_mul_of_nonneg_right h2 hu0
      _ = _ := by ring

/-- `57 ≤ k ≤ 1023`: as `mid_low_near`. -/
theorem large_near (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm57 : 57 ≤ m.toNat) (hm : m.toNat ≤ 1023) :
    ∃ S : ℝ, Finite (Expm1Words.kernel y c false m) ∧ 0 < S ∧
      |value (Expm1Words.kernel y c false m) - S| ≤ u * S ∧
      |S - ((2 : ℝ) ^ m.toNat * Real.exp r - 1)| ≤
        85 / 100 * u * ((2 : ℝ) ^ m.toNat * Real.exp r - 1) := by
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
  have h1v : value Expm1Words.one = 1 := const_values.1
  have hdb := abs_lt.mp hdm
  have hyr := F64AddBounds.sub_real_relative Expm1Words.one d const_finite.1 hdf (by
    rw [h1v, abs_lt]; constructor <;> linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  rw [h1v] at hyr
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
  have hp : (0 : ℝ) < 2 ^ m.toNat := by positivity
  refine ⟨2 ^ m.toNat * (1 - value d), hvf, by nlinarith, ?_, ?_⟩
  · rw [hvv, ← mul_sub, abs_mul, abs_of_pos hp, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ hp.le
    have := hyr.2
    rwa [abs_of_pos (by linarith : (0 : ℝ) < 1 - value d)] at this
  · have hsplit : (2 : ℝ) ^ m.toNat * (1 - value d) - (2 ^ m.toNat * Real.exp r - 1) =
        2 ^ m.toNat * ((1 - value d) - Real.exp r) + 1 := by ring
    rw [hsplit]
    have h1 : |(2 : ℝ) ^ m.toNat * ((1 - value d) - Real.exp r) + 1| ≤
        2 ^ m.toNat * (4901 / 10000 * u) + 1 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hp, abs_one]
      gcongr
    refine h1.trans ?_
    rw [hu]
    have h3 : (2 : ℝ) ^ 57 * (1 / 2 ^ 53) = 16 := by norm_num
    have h4 : (16 : ℝ) ≤ 2 ^ m.toNat * (1 / 2 ^ 53) := by rw [← h3]; gcongr
    nlinarith

#print axioms final_neg
#print axioms neg_one_near
#print axioms neg_k_near
#print axioms mid_low_near
#print axioms mid_high_near
#print axioms large_near

end Verified.Examples.Expm1NearForms
