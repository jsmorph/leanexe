import Library.Numerics.Float64.Tanh.Expm1NearForms

/-!
The forms of fdlibm's `expm1` for `k = 1` and `k = 2` with the error of the exact value before the
last rounding exported, for the positive arguments that `sinh` passes.  Each theorem gives a real
`S` of which the kernel's result is a nearest word, and bounds `S` against `2 ^ k exp r - 1`:
`4802/10000 u` for `k = 1` and `x < -1/4` (`one_low_near`), the same plus `3 η + 2 · 2 ^ -55`, or
`3 η + 2 · 2 ^ -56` below `1.49`, for `k = 1` and `x ≥ -1/4` (`one_high_near`), and
`4 · 0.4901 u` for `k = 2` (`two_near`).
-/

namespace Library.Numerics.Float64.Tanh.Expm1NearPos
open CodeLib.IEEE64 LeanExe.ProofKit Expm1KernelInner Expm1FormBase Expm1FormsOne Expm1FormsTwo

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem one_low_near (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hq : value y < -1 / 4) :
    ∃ S : ℝ, F64NearestNonnegative.Nearest S (Expm1Words.kernel y c false 1) ∧
      |S - (2 * Real.exp r - 1)| ≤ 4802 / 10000 * u := by
  obtain ⟨he2f, he2m, hV, -, hlo, hhi⟩ := common y c hyf hcf hy hc r hr
  have hu : u = 1 / 2 ^ 53 := u_value
  have hyb := abs_le.mp hy
  obtain ⟨haf, hav⟩ := add_half_exact y hyf hq (by linarith)
  set a := Wasm.IEEE64.add y Expm1Words.half
  set b := Wasm.IEEE64.sub (Expm1Words.e2 y c) a
  have hlt : Wasm.IEEE64.lt y Expm1Words.negQuarter = true := by
    rw [negQuarter_lt y hyf]; simp [hq]
  have hk : Expm1Words.kernel y c false 1 = Wasm.IEEE64.mul Expm1Words.negTwo b := by
    simp [Expm1Words.kernel, hlt, b, a]
  rw [hk]
  -- `b` rounds `e - (x + 1/2) = -(x - e) - 1/2 < 0`.
  have hV' := abs_le.mp hV
  have hsmall : 2401 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  have hbneg : value (Expm1Words.e2 y c) - value a < 0 := by rw [hav]; linarith
  have hnb := F64NearestSum.sub_nearest_neg _ _ he2f haf hbneg (by rw [hav]; linarith)
  have hrhi : r ≤ -(2499 / 10000) := by
    have h1 := abs_le.mp hr
    have h2 := abs_le.mp hc
    have h3 : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h4 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  have hexp : Real.exp r ≤ 7790 / 10000 :=
    (Real.exp_le_exp.mpr hrhi).trans exp_quarter_upper
  have hbs := F64NearestSum.sub_half_spacing (Expm1Words.e2 y c) a he2f haf 1020 (by
    rw [hav, abs_lt]; constructor <;> norm_num <;> linarith) (by norm_num)
  have hbf : Finite b := hbs.1
  obtain ⟨hnbf, hnbv⟩ := F64Magnitude.negate_value b hbf
  have hbm : |value (Wasm.IEEE64.negate b)| < 1 := by
    rw [hnbv, abs_neg]
    have := abs_le.mp hbs.2
    rw [hav] at this
    rw [abs_lt]; constructor <;> norm_num at this ⊢ <;> linarith
  have hb1 : |value (F64ExponentBounds.boundary 1023)| = 1 := by
    rw [F64ExponentBounds.boundary, F64PositiveSpacing.boundary_value 1023 (by norm_num)
      (by norm_num), abs_of_pos (by positivity)]
    norm_num
  have hbe := F64ExponentBounds.exponent_lt_of_magnitude_lt (Wasm.IEEE64.negate b) 1023
    (by norm_num) (by rw [hb1]; exact hbm)
  have hsc := F64NearestScale.scale_nearest _ _ 1 le_rfl (by norm_num) hnb (by
    rw [hav]; norm_num; linarith) (lt_of_lt_of_le (Nat.add_lt_add_right hbe 1) (by norm_num))
  rw [show (1023 + 1 : Nat) = 1024 by norm_num] at hsc
  rw [Expm1FormWords.mul_negTwo b hbf]
  refine ⟨_, hsc.2.2, ?_⟩
  rw [hav]
  have hsplit : (2 : ℝ) ^ 1 * -(value (Expm1Words.e2 y c) - (value y + 1 / 2)) -
      (2 * Real.exp r - 1) =
      2 * ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) := by ring
  rw [hsplit, abs_mul, abs_two]
  calc 2 * |(value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)| ≤
      2 * (2401 / 10000 * u) := by gcongr
    _ = 4802 / 10000 * u := by ring

theorem one_high_near (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hq : ¬ value y < -1 / 4) :
    ∃ S : ℝ, F64NearestNonnegative.Nearest S (Expm1Words.kernel y c false 1) ∧
      |S - (2 * Real.exp r - 1)| ≤ 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 55) ∧
      (2 * Real.exp r - 1 ≤ 149 / 100 →
        |S - (2 * Real.exp r - 1)| ≤ 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 56)) := by
  obtain ⟨he2f, -, hV, -, hlo, hhi⟩ := common y c hyf hcf hy hc r hr
  obtain ⟨hm, hdf, hd⟩ := diff_spec y c hyf he2f r hV hlo hhi
  have hu : u = 1 / 2 ^ 53 := u_value
  have hη : η = 1 / 2 ^ 1075 := eta_value
  set d := Wasm.IEEE64.sub y (Expm1Words.e2 y c)
  have hlt : Wasm.IEEE64.lt y Expm1Words.negQuarter = false := by
    rw [negQuarter_lt y hyf]; simp [hq]
  have hk : Expm1Words.kernel y c false 1 =
      Wasm.IEEE64.add Expm1Words.one (Wasm.IEEE64.mul Expm1Words.two d) := by
    simp [Expm1Words.kernel, hlt, d]
  rw [hk]
  have hdm : |value d| < 4146 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value d) (value y - value (Expm1Words.e2 y c))
    have h1 : (1 : ℝ) / 2 ^ 55 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  obtain ⟨hddf, hdd⟩ := Expm1FormWords.double_spec d hdf (hdm.trans (by norm_num))
  have h1v : value Expm1Words.one = 1 := const_values.1
  have hddb := abs_le.mp hdd
  have hdmb := abs_lt.mp hdm
  have hη1 : 3 * η ≤ 1 / 10 ^ 10 := by rw [hη]; norm_num
  have hnear := F64NearestSum.add_nearest Expm1Words.one _ const_finite.1 hddf
    (by rw [h1v]; linarith) (by rw [h1v]; linarith)
  rw [h1v] at hnear
  have hsplit : 1 + value (Wasm.IEEE64.mul Expm1Words.two d) - (2 * Real.exp r - 1) =
      (value (Wasm.IEEE64.mul Expm1Words.two d) - 2 * value d) +
        2 * (value d - (value y - value (Expm1Words.e2 y c))) +
        2 * ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) := by ring
  have hbound : ∀ g : ℝ, |value d - (value y - value (Expm1Words.e2 y c))| ≤ g →
      |1 + value (Wasm.IEEE64.mul Expm1Words.two d) - (2 * Real.exp r - 1)| ≤
        4802 / 10000 * u + 3 * η + 2 * g := by
    intro g hg
    rw [hsplit]
    calc _ ≤ |value (Wasm.IEEE64.mul Expm1Words.two d) - 2 * value d| +
          |2 * (value d - (value y - value (Expm1Words.e2 y c)))| +
          |2 * ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1))| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3 * η + 2 * g + 2 * (2401 / 10000 * u) := by
          rw [abs_mul, abs_mul, abs_two]
          gcongr
      _ = _ := by ring
  refine ⟨_, hnear, hbound _ hd, fun hsmall => hbound _ ?_⟩
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  have hrlow : -(2501 / 10000) ≤ r := by
    have h1 := abs_le.mp hr
    have h2 := abs_le.mp hc
    have h3 : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h4 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    have hq' := not_lt.mp hq
    linarith
  have hexp : 7787 / 10000 ≤ Real.exp r :=
    exp_quarter_lower.trans (Real.exp_le_exp.mpr hrlow)
  have h4 : |value y - value (Expm1Words.e2 y c)| < (2 : ℝ) ^ (53 + 1019) / 2 ^ 1074 := by
    rw [show (2 : ℝ) ^ (53 + 1019) / 2 ^ 1074 = 1 / 4 by norm_num, abs_lt]
    have h5 : 2401 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    constructor <;> linarith
  have hs := F64NearestSum.sub_half_spacing y (Expm1Words.e2 y c) hyf he2f 1019 h4 (by norm_num)
  rw [show (2 : ℝ) ^ 1019 / 2 / 2 ^ 1074 = 1 / 2 ^ 56 by norm_num] at hs
  exact hs.2

theorem two_near (y c : UInt64) (m : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hm2 : m.toNat = 2) :
    ∃ S : ℝ, F64NearestNonnegative.Nearest S (Expm1Words.kernel y c false m) ∧
      |S - (4 * Real.exp r - 1)| ≤ 4 * (4901 / 10000 * u) := by
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
  obtain ⟨htf, htv⟩ := Expm1FormWords.oneMinus_spec m (by omega) (by omega)
  have hpm : (2 : ℝ) ^ m.toNat = 4 := by rw [hm2]; norm_num
  have hdb := abs_lt.mp hdm
  have hsmall : 4901 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
  have hs1b := abs_le.mp hs1
  rw [hpm] at htv
  have hsb : 45 / 100 ≤ value (Expm1Words.oneMinus m) - value d := by rw [htv]; linarith
  have hnb := F64NearestSum.sub_nearest _ d htf hdf (by linarith) (by rw [htv]; linarith)
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
  rw [hpm] at hsc
  refine ⟨_, hsc.2.2, ?_⟩
  rw [htv, show 4 * (1 - 1 / 4 - value d) - (4 * Real.exp r - 1) =
    4 * ((1 - value d) - Real.exp r) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact mul_le_mul_of_nonneg_left hs1 (by norm_num)

#print axioms one_low_near
#print axioms one_high_near
#print axioms two_near

end Library.Numerics.Float64.Tanh.Expm1NearPos
