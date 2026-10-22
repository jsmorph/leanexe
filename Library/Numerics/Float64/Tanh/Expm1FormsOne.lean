import Library.Numerics.Float64.Tanh.Expm1FormBase
import Library.Numerics.Float64.Tanh.Expm1FormWords
import LeanExe.ProofKit.F64GridExact

/-!
The three forms of fdlibm's `expm1` for `k = ±1`, each within one step of `2 ^ k exp r - 1`.
For `k = -1` the kernel returns `(x - e)/2 - 1/2`; for `k = 1` and `x < -1/4` it returns
`-2 (e - (x + 1/2))`, where `x + 1/2` is exact; and for `k = 1` and `x ≥ -1/4` it returns
`1 + 2 (x - e)`.  Here `x - e` stands for `value y - value e2`, which `common` places within
`0.2401 u` of `exp r - 1`.
-/

namespace Library.Numerics.Float64.Tanh.Expm1FormsOne
open CodeLib.IEEE64 LeanExe.ProofKit Expm1KernelInner Expm1FormBase

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- `lt` on finite words compares values. -/
theorem lt_value (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.lt a b = decide (value a < value b) := by
  simp only [Wasm.IEEE64.lt, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_self,
    Bool.false_eq_true, ite_false, value]
  congr 1
  apply propext
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

/-- `x - e` and its rounding, below `1/2` in magnitude. -/
theorem diff_spec (y c : UInt64) (hyf : Finite y) (he2f : Finite (Expm1Words.e2 y c)) (r : ℝ)
    (hV : |(value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)| ≤ 2401 / 10000 * u)
    (hlo : 7070 / 10000 ≤ Real.exp r) (hhi : Real.exp r ≤ 14143 / 10000) :
    |value y - value (Expm1Words.e2 y c)| < 4145 / 10000 ∧
      Finite (Wasm.IEEE64.sub y (Expm1Words.e2 y c)) ∧
      |value (Wasm.IEEE64.sub y (Expm1Words.e2 y c)) - (value y - value (Expm1Words.e2 y c))| ≤
        1 / 2 ^ 55 := by
  have hu : u = 1 / 2 ^ 53 := u_value
  have hm : |value y - value (Expm1Words.e2 y c)| < 4145 / 10000 := by
    have := abs_le.mp hV
    have h1 : 2401 / 10000 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    rw [abs_lt]; constructor <;> linarith
  have hs := F64NearestSum.sub_half_spacing y (Expm1Words.e2 y c) hyf he2f 1020
    (hm.trans (by norm_num)) (by norm_num)
  exact ⟨hm, hs.1, hs.2.trans (le_of_eq (by norm_num))⟩

/-- `k = -1`: `(x - e)/2 - 1/2`. -/
theorem form_neg_one (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) :
    F64SignedRounding.WithinSteps 1 (Real.exp r / 2 - 1) (Expm1Words.kernel y c true 1) := by
  obtain ⟨he2f, -, hV, -, hlo, hhi⟩ := common y c hyf hcf hy hc r hr
  obtain ⟨hm, hdf, hd⟩ := diff_spec y c hyf he2f r hV hlo hhi
  have hu : u = 1 / 2 ^ 53 := u_value
  have hη : η = 1 / 2 ^ 1075 := eta_value
  set d := Wasm.IEEE64.sub y (Expm1Words.e2 y c)
  obtain ⟨hhf, hh⟩ := hfx_spec d hdf
  set h := Expm1Words.hfx d
  have hk : Expm1Words.kernel y c true 1 = Wasm.IEEE64.sub h Expm1Words.half := by
    simp [Expm1Words.kernel, h, d, Expm1Words.hfx]
  rw [hk]
  have hhalf : value Expm1Words.half = 1 / 2 := const_values.2.1
  have hfh : Finite Expm1Words.half := const_finite.2.1
  have hdm : |value d| < 4146 / 10000 := by
    have := abs_sub_abs_le_abs_sub (value d) (value y - value (Expm1Words.e2 y c))
    have h1 : (1 : ℝ) / 2 ^ 55 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  have hneg : value h - value Expm1Words.half < 0 := by
    rw [hhalf]
    have := abs_le.mp hh
    have h1 : 2 * η ≤ 1 / 10 ^ 10 := by rw [hη]; norm_num
    have := abs_lt.mp hdm
    linarith
  have hnear := F64NearestSum.sub_nearest_neg h _ hhf hfh hneg (by
    rw [hhalf]
    have := abs_le.mp hh
    have h1 : 2 * η ≤ 1 / 10 ^ 10 := by rw [hη]; norm_num
    have := abs_lt.mp hdm
    have h2 : -(2 : ℝ) ^ 1023 < -1 := by norm_num
    linarith)
  apply (F64SignedRounding.within_negate 1 _ _).mp
  refine within_of_level _ _ _ 1021 (by norm_num) (by norm_num) ?_ ?_ hnear ?_
  · norm_num; linarith
  · have : -(Real.exp r / 2 - 1) ≤ 1 := by linarith [Real.exp_pos r]
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · rw [hhalf]
    have hsplit : -(value h - 1 / 2) - -(Real.exp r / 2 - 1) =
        -((value h - value d / 2) + (value d - (value y - value (Expm1Words.e2 y c))) / 2 +
          ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) / 2) := by ring
    rw [hsplit, abs_neg]
    calc _ ≤ |value h - value d / 2| + |(value d - (value y - value (Expm1Words.e2 y c))) / 2| +
          |((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) / 2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * η + 1 / 2 ^ 55 / 2 + 2401 / 10000 * u / 2 := by
          rw [abs_div, abs_div, abs_two]
          gcongr
      _ < (2 : ℝ) ^ (1021 - 1) / 2 ^ 1074 := by rw [hu, hη]; norm_num

/-- The word of `-1/4`. -/
theorem negQuarter_lt (y : UInt64) (hyf : Finite y) :
    Wasm.IEEE64.lt y Expm1Words.negQuarter = decide (value y < -1 / 4) := by
  rw [lt_value y _ hyf const_finite.2.2.2.2.2.2.1, const_values.2.2.2.2.2.2]

/-- A value in `[1/4, 1/2)` in magnitude has exponent field 1021. -/
theorem exponent_quarter (y : UInt64) (hlo : 1 / 4 ≤ |value y|) (hhi : |value y| < 1 / 2) :
    Wasm.IEEE64.exponent y = 1021 := by
  have hb1 : |value (F64ExponentBounds.boundary 1022)| = 1 / 2 := by
    rw [F64ExponentBounds.boundary, F64PositiveSpacing.boundary_value 1022 (by norm_num)
      (by norm_num), abs_of_pos (by positivity)]
    norm_num
  have hlt := F64ExponentBounds.exponent_lt_of_magnitude_lt y 1022 (by norm_num)
    (by rw [hb1]; exact hhi)
  have hge : 1021 ≤ Wasm.IEEE64.exponent y := by
    by_contra hn
    have := F64Magnitude.magnitude_lt y 1021 (-2) (by norm_num) (by norm_num) (by omega)
    norm_num at this
    linarith
  omega

/-- `x + 1/2` is exact for `x` in `[-1/2, -1/4]`. -/
theorem add_half_exact (y : UInt64) (hyf : Finite y) (hneg : value y < -1 / 4)
    (hy : -1 / 2 < value y) :
    Finite (Wasm.IEEE64.add y Expm1Words.half) ∧
      value (Wasm.IEEE64.add y Expm1Words.half) = value y + 1 / 2 := by
  have hfh : Finite Expm1Words.half := const_finite.2.1
  have hhalf : value Expm1Words.half = 1 / 2 := const_values.2.1
  have he := exponent_quarter y (by rw [abs_of_neg (by linarith)]; linarith)
    (by rw [abs_of_neg (by linarith)]; linarith)
  have hs : Wasm.IEEE64.sign y = true := by
    have hm : 0 < Wasm.IEEE64.scaledMagnitude y := by
      unfold Wasm.IEEE64.scaledMagnitude; simp [he]
    exact (F64Magnitude.sign_value y hm).mpr (by linarith)
  have hf : Wasm.IEEE64.fraction y < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have hsv : Wasm.IEEE64.scaledValue y = -(((2 ^ 52 + Wasm.IEEE64.fraction y : Nat) : ℤ) * 2 ^ 1020) := by
    simp only [Wasm.IEEE64.scaledValue, hs, ite_true, Wasm.IEEE64.scaledMagnitude, he]
    push_cast
    ring_nf
  have hhv : Wasm.IEEE64.scaledValue Expm1Words.half = 2 ^ 53 * 2 ^ 1020 := by decide +kernel
  have hsum : Wasm.IEEE64.scaledValue y + Wasm.IEEE64.scaledValue Expm1Words.half =
      ((2 ^ 52 : ℤ) - Wasm.IEEE64.fraction y) * 2 ^ 1020 := by
    rw [hsv, hhv]; push_cast; ring
  have hz : ((2 ^ 52 : ℤ) - Wasm.IEEE64.fraction y).natAbs ≤ 2 ^ 53 := by
    have : (0 : ℤ) ≤ 2 ^ 52 - Wasm.IEEE64.fraction y := by
      have : (Wasm.IEEE64.fraction y : ℤ) < 2 ^ 52 := by exact_mod_cast hf
      linarith
    omega
  obtain ⟨hf', hv⟩ := F64GridExact.grid_add_exact y _ hyf hfh _ 1020 hsum hz (by norm_num)
  refine ⟨hf', ?_⟩
  rw [value, hv, Int.cast_add, add_div]
  rw [← hhalf]
  rfl

theorem exp_quarter_upper : Real.exp (-(2499 / 10000)) ≤ 7790 / 10000 := by
  have hup := TaylorRemainder.exp_remainder (-(2499 / 10000)) (by norm_num) 8 (by norm_num)
  rw [expCoeffs_eight] at hup
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at hup
  norm_num [Nat.factorial] at hup
  have := (abs_le.mp hup).2
  linarith

/-- `k = 1` and `x < -1/4`: `-2 (e - (x + 1/2))`. -/
theorem form_one_low (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hq : value y < -1 / 4) :
    F64SignedRounding.WithinSteps 1 (2 * Real.exp r - 1) (Expm1Words.kernel y c false 1) := by
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
  refine within_of_level _ _ _ 1021 (by norm_num) (by norm_num) ?_ ?_ hsc.2.2 ?_
  · norm_num; linarith
  · have : 2 * Real.exp r - 1 ≤ 2 := by linarith
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · rw [hav]
    have hsplit : (2 : ℝ) ^ 1 * -(value (Expm1Words.e2 y c) - (value y + 1 / 2)) -
        (2 * Real.exp r - 1) =
        2 * ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) := by ring
    rw [hsplit, abs_mul, abs_two]
    calc 2 * |(value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)| ≤
        2 * (2401 / 10000 * u) := by gcongr
      _ < (2 : ℝ) ^ (1021 - 1) / 2 ^ 1074 := by rw [hu]; norm_num

theorem exp_quarter_lower : 7787 / 10000 ≤ Real.exp (-(2501 / 10000)) := by
  have hlo := TaylorRemainder.exp_remainder (-(2501 / 10000)) (by norm_num) 8 (by norm_num)
  rw [expCoeffs_eight] at hlo
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at hlo
  norm_num [Nat.factorial] at hlo
  have := (abs_le.mp hlo).1
  linarith

/-- `k = 1` and `x ≥ -1/4`: `1 + 2 (x - e)`. -/
theorem form_one_high (y c : UInt64) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) (hq : ¬ value y < -1 / 4) :
    F64SignedRounding.WithinSteps 1 (2 * Real.exp r - 1) (Expm1Words.kernel y c false 1) := by
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
  -- `r ≥ -0.2501`, so `2 exp r - 1 ≥ 0.557`.
  have hrlow : -(2501 / 10000) ≤ r := by
    have h1 := abs_le.mp hr
    have h2 := abs_le.mp hc
    have h3 : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h4 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    have hq' := not_lt.mp hq
    linarith
  have hexp : 7787 / 10000 ≤ Real.exp r :=
    exp_quarter_lower.trans (Real.exp_le_exp.mpr hrlow)
  refine within_of_level _ _ _ 1022 (by norm_num) (by norm_num) ?_ ?_ hnear ?_
  · norm_num; linarith
  · have : 2 * Real.exp r - 1 ≤ 2 := by linarith
    exact lt_of_le_of_lt this (by unfold F64PositiveRounding.overflowThreshold; norm_num)
  · have hsplit : 1 + value (Wasm.IEEE64.mul Expm1Words.two d) - (2 * Real.exp r - 1) =
        (value (Wasm.IEEE64.mul Expm1Words.two d) - 2 * value d) +
          2 * (value d - (value y - value (Expm1Words.e2 y c))) +
          2 * ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)) := by ring
    rw [hsplit]
    calc _ ≤ |value (Wasm.IEEE64.mul Expm1Words.two d) - 2 * value d| +
          |2 * (value d - (value y - value (Expm1Words.e2 y c)))| +
          |2 * ((value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1))| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3 * η + 2 * (1 / 2 ^ 55) + 2 * (2401 / 10000 * u) := by
          rw [abs_mul, abs_mul, abs_two]
          gcongr
      _ < (2 : ℝ) ^ (1022 - 1) / 2 ^ 1074 := by rw [hu, hη]; norm_num

#print axioms lt_value
#print axioms form_neg_one
#print axioms add_half_exact
#print axioms exp_quarter_upper
#print axioms form_one_low
#print axioms form_one_high

end Library.Numerics.Float64.Tanh.Expm1FormsOne
