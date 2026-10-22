import Library.Numerics.Float64.Erf.ErfTailEval

/-!
The relative error of `s_erf.c`'s tail quotient `exp (-z² - 0.5625) exp (t)/x` against `erfc x`.
`x erfc x = exp (-z² - 9/16) exp ((z - x)(z + x) + R/S (1/x²) - tailF x)` (`x_erfc`), so relative
errors `k` of the two exponentials, an error `δ` of the computed `t`, the kernel's `τ`, and the
roundings of the product and the quotient compose into `tailEps k (δ + τ) =
(1 + k)² (1 + u)² (1 + d + d²) - 1` (`tail_compose`), where `1 + d + d²` bounds `exp d` for
`d ≤ 1/2`.  `erfc_five_fourths` bounds `erfc 1.25` by `0.0772` from `erf_series`, and
`tail_erf` turns a relative error `ε` with `0.0772 ε < 2^-53` into one step for `erf x = 1 - erfc x`
through the nearest rounding of `1 - q`.
-/

namespace Library.Numerics.Float64.Erf.ErfTailCompose
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64ErrorTrack F64Horner RealErf ErfTailBase
  ErfTailCoeffs ErfSmallBase ErfKernelSmall

set_option exponentiation.threshold 4096

/-- The composed relative error. -/
def tailEps (k d : ℚ) : ℚ := (1 + k) ^ 2 * (1 + uQ) ^ 2 * (1 + d + d ^ 2) - 1

/-- `x erfc x` in terms of the tail model. -/
theorem x_erfc (R S : List ℚ) (x z : ℝ) (hx : 0 < x) :
    x * RealErf.erfc x = Real.exp (-z ^ 2 - 9 / 16) *
      Real.exp ((z - x) * (z + x) + eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹ - tailF R S x) := by
  have hpos : 0 < x * erfcx x := mul_pos hx (erfcx_pos x)
  have h1 : (z - x) * (z + x) + eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹ - tailF R S x =
      z ^ 2 - x ^ 2 + 9 / 16 + Real.log (x * erfcx x) := by
    simp only [tailF, tailW]
    ring
  rw [h1, ← Real.exp_add, show -z ^ 2 - 9 / 16 + (z ^ 2 - x ^ 2 + 9 / 16 + Real.log (x * erfcx x)) =
    -x ^ 2 + Real.log (x * erfcx x) by ring, Real.exp_add, Real.exp_log hpos, erfc_eq]
  ring

/-- Relative errors of positive factors compose. -/
theorem rel_mul {a A b B α β : ℝ} (hA : 0 < A) (hB : 0 < B) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : |a - A| ≤ α * A) (hb : |b - B| ≤ β * B) :
    |a * b - A * B| ≤ ((1 + α) * (1 + β) - 1) * (A * B) := by
  have hb' : |b| ≤ (1 + β) * B := by
    have := abs_sub_abs_le_abs_sub b B
    rw [abs_of_pos hB] at this
    linarith
  have heq : a * b - A * B = (a - A) * b + A * (b - B) := by ring
  rw [heq]
  calc |(a - A) * b + A * (b - B)| ≤ |(a - A) * b| + |A * (b - B)| := abs_add_le _ _
    _ = |a - A| * |b| + A * |b - B| := by rw [abs_mul, abs_mul, abs_of_pos hA]
    _ ≤ (α * A) * ((1 + β) * B) + A * (β * B) := by
        apply add_le_add
        · exact mul_le_mul ha hb' (abs_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left hb hA.le
    _ = ((1 + α) * (1 + β) - 1) * (A * B) := by ring

/-- `|exp w - 1| ≤ d + d²` for `|w| ≤ d ≤ 1`. -/
theorem exp_near_one (w d : ℝ) (hw : |w| ≤ d) (hd : d ≤ 1) : |Real.exp w - 1| ≤ d + d ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := w) (hw.trans hd)
  have h2 : w ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  have h3 := abs_sub_le (Real.exp w - 1) w 0
  rw [sub_zero, sub_zero] at h3
  have h4 : |Real.exp w - 1 - w| = |Real.exp w - 1 - w| := rfl
  linarith

/-- The relative error of the tail quotient. -/
theorem tail_compose (R S : List ℚ) (k d : ℚ) (hk : 0 ≤ k) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hk1 : k ≤ 1 / 2 ^ 40) (X Z A1 A2 E1 E2 : UInt64) (hX : Finite X) (hx1 : 1 ≤ value X)
    (hx32 : value X ≤ 32) (hy : 1 / 2 ^ 1000 ≤ RealErf.erfc (value X))
    (hA1 : value A1 = -(value Z) ^ 2 - 9 / 16)
    (hE1 : Finite E1 ∧ |value E1 - Real.exp (value A1)| ≤ k * Real.exp (value A1))
    (hE2 : Finite E2 ∧ |value E2 - Real.exp (value A2)| ≤ k * Real.exp (value A2))
    (hA2 : |value A2 - ((value Z - value X) * (value Z + value X) +
      eval R (value X ^ 2)⁻¹ / eval S (value X ^ 2)⁻¹)| + |tailF R S (value X)| ≤ d) :
    Finite (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X) ∧
      |value (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X) - RealErf.erfc (value X)| ≤
        (tailEps k d : ℝ) * RealErf.erfc (value X) := by
  have hu : unitRoundoff64 = ((uQ : ℚ) : ℝ) := uQ_eq.symm
  have hu0 : (uQ : ℝ) = 1 / 2 ^ 53 := by simp [uQ]
  set x := value X
  set z := value Z
  set T := (z - x) * (z + x) + eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹
  have hx0 : 0 < x := by linarith
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd0
  have hd2 : (d : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hd
    push_cast at h
    exact h
  have hk1' : (k : ℝ) ≤ 1 / 2 ^ 40 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hk1
    push_cast at h
    exact h
  set C := Real.exp (T - tailF R S x)
  have hC : 0 < C := Real.exp_pos _
  have hA1p : 0 < Real.exp (value A1) := Real.exp_pos _
  have hxe : x * RealErf.erfc x = Real.exp (value A1) * C := by
    rw [hA1, x_erfc R S x z hx0]
  -- the second exponential against `C`
  have hw : |value A2 - (T - tailF R S x)| ≤ d := by
    have := abs_sub_le (value A2) T (T - tailF R S x)
    have h2 : |T - (T - tailF R S x)| = |tailF R S x| := by ring_nf
    linarith
  have hexp := exp_near_one (value A2 - (T - tailF R S x)) d hw (by linarith)
  have hA2C : Real.exp (value A2) = C * Real.exp (value A2 - (T - tailF R S x)) := by
    rw [← Real.exp_add]
    ring_nf
  have hq1 : (1 : ℝ) ≤ 1 + d + d ^ 2 := by linarith only [hd', sq_nonneg (d : ℝ)]
  have hq2 : (1 + d + d ^ 2 : ℝ) ≤ 7 / 4 := by
    have h := pow_le_pow_left₀ hd' hd2 2
    have h' : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    linarith only [h, h', hd2]
  have hE2C : |value E2 - C| ≤ ((1 + k) * (1 + d + d ^ 2) - 1) * C := by
    have h2 : |Real.exp (value A2) - C| ≤ (d + d ^ 2) * C := by
      rw [hA2C, show C * Real.exp (value A2 - (T - tailF R S x)) - C =
        C * (Real.exp (value A2 - (T - tailF R S x)) - 1) by ring, abs_mul, abs_of_pos hC]
      have := mul_le_mul_of_nonneg_left hexp hC.le
      linarith only [this]
    have h3 : Real.exp (value A2) ≤ (1 + d + d ^ 2) * C := by
      have := (abs_le.mp h2).2
      linarith only [this]
    have h4 : (k : ℝ) * Real.exp (value A2) ≤ k * ((1 + d + d ^ 2) * C) :=
      mul_le_mul_of_nonneg_left h3 hk'
    have h5 := abs_sub_le (value E2) (Real.exp (value A2)) C
    have h6 : ((1 + k) * (1 + d + d ^ 2) - 1) * C = k * ((1 + d + d ^ 2) * C) + (d + d ^ 2) * C := by
      ring
    rw [h6]
    linarith only [h5, hE2.2, h4, h2]
  have hβ : (0 : ℝ) ≤ (1 + k) * (1 + d + d ^ 2) - 1 := by
    have := one_le_mul_of_one_le_of_one_le (show (1 : ℝ) ≤ 1 + k by linarith only [hk']) hq1
    linarith only [this]
  -- the exact product of the two computed exponentials
  have hprod := rel_mul hA1p hC hk' hβ hE1.2 hE2C
  rw [← hxe] at hprod
  set K1 : ℝ := (1 + k) * (1 + ((1 + k) * (1 + d + d ^ 2) - 1)) - 1
  have hK1 : K1 = (1 + k) ^ 2 * (1 + d + d ^ 2) - 1 := by ring
  have hK1s : K1 ≤ 4 / 5 := by
    rw [hK1]
    have h1 : (1 + (k : ℝ)) ^ 2 ≤ (1 + 1 / 2 ^ 40) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hk']) (by linarith only [hk1']) 2
    have h3 := mul_le_mul h1 hq2 (by linarith only [hq1]) (by positivity)
    have h4 : ((1 : ℝ) + 1 / 2 ^ 40) ^ 2 * (7 / 4) - 1 ≤ 4 / 5 := by norm_num
    linarith only [h3, h4]
  have hK10 : 0 ≤ K1 := by
    rw [hK1]
    have h1 : (1 : ℝ) ≤ (1 + (k : ℝ)) ^ 2 := one_le_pow₀ (by linarith only [hk'])
    have := one_le_mul_of_one_le_of_one_le h1 hq1
    linarith only [this]
  set y := x * RealErf.erfc x
  have hey : 0 < RealErf.erfc x := erfc_pos x
  have hy0 : 0 < y := mul_pos hx0 hey
  have hyl : 1 / 2 ^ 1000 ≤ y := by
    have : RealErf.erfc x ≤ x * RealErf.erfc x := le_mul_of_one_le_left hey.le hx1
    linarith only [this, hy]
  have hyu : y ≤ 64 := by
    have h1 := mul_le_mul hx32 (erfc_lt_two x).le hey.le (by norm_num)
    linarith only [h1]
  set P := value E1 * value E2
  have hK1y : K1 * y ≤ 4 / 5 * y := mul_le_mul_of_nonneg_right hK1s hy0.le
  have hK1y0 : 0 ≤ K1 * y := mul_nonneg hK10 hy0.le
  have hPl : y / 5 ≤ P := by
    have := (abs_le.mp hprod).1
    linarith only [this, hK1y]
  have hPu : P ≤ 2 * y := by
    have := (abs_le.mp hprod).2
    linarith only [this, hK1y, hy0]
  have hmN : minNormal64 = 1 / 2 ^ 1022 := rfl
  have hPm : minNormal64 ≤ |P| := by
    rw [abs_of_pos (show (0 : ℝ) < P by linarith only [hPl, hy0]), hmN]
    have : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 1000 / 5 := by norm_num
    linarith only [this, hPl, hyl]
  obtain ⟨hrf, hre⟩ := F64MulBounds.mul_real_adaptive E1 E2 hE1.1 hE2.1 (by
    rw [abs_of_pos (show (0 : ℝ) < value E1 * value E2 by linarith only [hPl, hy0])]
    linarith only [hPu, hyu, show (128 : ℝ) < 2 ^ 1022 by norm_num])
  have hr : |value (Wasm.IEEE64.mul E1 E2) - P| ≤ unitRoundoff64 * |P| := by
    simp only at hre
    split_ifs at hre with hn
    · have h0 : (0 : ℝ) ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
      have : (0 : ℝ) ≤ unitRoundoff64 * |P| := mul_nonneg h0 (abs_nonneg _)
      rw [mul_zero] at hre
      linarith only [hre, this]
    · rwa [max_eq_left hPm] at hre
  set r := value (Wasm.IEEE64.mul E1 E2)
  have hu' : (0 : ℝ) ≤ unitRoundoff64 := by rw [hu, hu0]; positivity
  have hry : |r - y| ≤ ((1 + K1) * (1 + unitRoundoff64) - 1) * y := by
    have h1 : |P| ≤ (1 + K1) * y := by
      rw [abs_of_pos (show (0 : ℝ) < P by linarith only [hPl, hy0])]
      have := (abs_le.mp hprod).2
      linarith only [this]
    have h2 := abs_sub_le r P y
    have h3 : unitRoundoff64 * |P| ≤ unitRoundoff64 * ((1 + K1) * y) :=
      mul_le_mul_of_nonneg_left h1 hu'
    have h4 : ((1 + K1) * (1 + unitRoundoff64) - 1) * y = K1 * y + unitRoundoff64 * ((1 + K1) * y) := by
      ring
    rw [h4]
    linarith only [h2, hr, h3, hprod]
  set K2 : ℝ := (1 + K1) * (1 + unitRoundoff64) - 1
  have huu : unitRoundoff64 ≤ 1 / 2 ^ 53 := by rw [hu, hu0]
  have hK2 : K2 ≤ 5 / 6 := by
    have h1 := mul_le_mul (show 1 + K1 ≤ 9 / 5 by linarith only [hK1s])
      (show 1 + unitRoundoff64 ≤ 1 + 1 / 2 ^ 53 by linarith only [huu]) (by linarith only [hu'])
      (by norm_num)
    have h2 : (9 : ℝ) / 5 * (1 + 1 / 2 ^ 53) - 1 ≤ 5 / 6 := by norm_num
    linarith only [h1, h2]
  have hK20 : 0 ≤ K2 := by
    have := one_le_mul_of_one_le_of_one_le (show (1 : ℝ) ≤ 1 + K1 by linarith only [hK10])
      (show (1 : ℝ) ≤ 1 + unitRoundoff64 by linarith only [hu'])
    linarith only [this]
  have hK2y : K2 * y ≤ 5 / 6 * y := mul_le_mul_of_nonneg_right hK2 hy0.le
  have hrl : y / 6 ≤ r := by
    have := (abs_le.mp hry).1
    linarith only [this, hK2y]
  have hrxs : Wasm.IEEE64.scaledMagnitude X ≠ 0 := by
    intro h0
    have : x = 0 := by
      simp only [x, value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    linarith only [this, hx0]
  have hru : r ≤ 128 := by
    have := (abs_le.mp hry).2
    linarith only [this, hK2y, hyu]
  have hrx : |r / x| < (2 : ℝ) ^ 1022 := by
    rw [abs_div, abs_of_pos (by linarith only [hrl, hy0] : 0 < r), abs_of_pos hx0, div_lt_iff₀ hx0]
    linarith only [hru, hx1, show (128 : ℝ) < 2 ^ 1022 by norm_num,
      mul_le_mul_of_nonneg_left hx1 (show (0 : ℝ) ≤ 2 ^ 1022 by positivity)]
  obtain ⟨hqf, hqe⟩ := F64DivApprox.div_real_adaptive _ X hrf hX hrxs hrx
  refine ⟨hqf, ?_⟩
  have hrxm : minNormal64 ≤ |r / x| := by
    rw [abs_div, abs_of_pos (by linarith only [hrl, hy0] : 0 < r), abs_of_pos hx0, hmN,
      le_div_iff₀ hx0]
    have h1 := mul_le_mul_of_nonneg_left hy hx0.le
    have h2 : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 1000 / 6 := by norm_num
    have h3 := mul_le_mul_of_nonneg_left h2 hx0.le
    have hyx : y = x * RealErf.erfc x := rfl
    linarith only [h1, h3, hrl, hyx]
  rw [max_eq_left hrxm] at hqe
  have hrxe : |r / x - RealErf.erfc x| ≤ K2 * RealErf.erfc x := by
    have h : r / x - RealErf.erfc x = (r - y) / x := by
      simp only [y]
      field_simp
    rw [h, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    have hyx : K2 * y = K2 * RealErf.erfc x * x := by simp only [y]; ring
    linarith only [hry, hyx]
  have hrxa : |r / x| ≤ (1 + K2) * RealErf.erfc x := by
    have := abs_sub_abs_le_abs_sub (r / x) (RealErf.erfc x)
    rw [abs_of_pos hey] at this
    linarith only [this, hrxe]
  have htot : |value (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X) - RealErf.erfc x| ≤
      ((1 + K2) * (1 + unitRoundoff64) - 1) * RealErf.erfc x := by
    have h1 := abs_sub_le (value (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X)) (r / x) (RealErf.erfc x)
    have h2 : unitRoundoff64 * |r / x| ≤ unitRoundoff64 * ((1 + K2) * RealErf.erfc x) :=
      mul_le_mul_of_nonneg_left hrxa hu'
    have h3 : ((1 + K2) * (1 + unitRoundoff64) - 1) * RealErf.erfc x =
        K2 * RealErf.erfc x + unitRoundoff64 * ((1 + K2) * RealErf.erfc x) := by ring
    rw [h3]
    linarith only [h1, hqe, h2, hrxe]
  refine htot.trans (le_of_eq ?_)
  simp only [K2, hK1, tailEps]
  rw [hu]
  push_cast
  ring

/-- `erfc 1.25 ≤ 0.0772`, from 20 terms of `erf_series`. -/
theorem erfc_five_fourths : RealErf.erfc (5 / 4) ≤ 772 / 10000 := by
  have hs := erf_series 20 (5 / 4)
  have hk := scale_bounds
  have hc := ErfTailBase.eval_cast (erfCoeffs 20) (25 / 16)
  have hp : (evalQ (erfCoeffs 20) (25 / 16) : ℚ) = evalQ (erfCoeffs 20) (25 / 16) := rfl
  have hcheck : (333038747416263463341 / 2 ^ 68 : ℚ) * (5 / 4) * evalQ (erfCoeffs 20) (25 / 16) -
      333038747416263463344 / 2 ^ 68 * ((5 / 4) ^ 41 / 99748982335242240000) ≥ 1 - 772 / 10000 := by
    decide +kernel
  have hE : (0 : ℝ) ≤ ((evalQ (erfCoeffs 20) (25 / 16) : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ evalQ (erfCoeffs 20) (25 / 16) := by decide +kernel
    exact_mod_cast this
  have hx2 : ((5 : ℝ) / 4) ^ 2 = ((25 / 16 : ℚ) : ℝ) := by norm_num
  rw [hx2, hc] at hs
  have hf : ((Nat.factorial 20 * (2 * 20 + 1) : ℕ) : ℝ) = 99748982335242240000 := by
    norm_num [Nat.factorial]
  rw [hf, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at hs
  have hcheck' : ((333038747416263463341 / 2 ^ 68 : ℚ) : ℝ) * (5 / 4) *
      ((evalQ (erfCoeffs 20) (25 / 16) : ℚ) : ℝ) -
      ((333038747416263463344 / 2 ^ 68 : ℚ) : ℝ) * ((5 / 4) ^ 41 / 99748982335242240000) ≥
      1 - 772 / 10000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcheck
    push_cast at h ⊢
    linarith
  have h1 := (abs_le.mp hs).1
  push_cast at hcheck'
  have h2 : (333038747416263463341 / 2 ^ 68 : ℝ) * (5 / 4 * ((evalQ (erfCoeffs 20) (25 / 16) : ℚ) : ℝ)) ≤
      scale * (5 / 4 * ((evalQ (erfCoeffs 20) (25 / 16) : ℚ) : ℝ)) :=
    mul_le_mul_of_nonneg_right hk.1 (by positivity)
  have h3 : scale * (((5 : ℝ) / 4) ^ (2 * 20 + 1) / 99748982335242240000) ≤
      (333038747416263463344 / 2 ^ 68) * ((5 / 4) ^ 41 / 99748982335242240000) :=
    mul_le_mul_of_nonneg_right hk.2 (by positivity)
  simp only [RealErf.erfc]
  norm_num at h1 h3 hcheck' ⊢
  linarith

/-- The criterion for one step of `erf` from a relative error of `erfc` on `[xlo, xhi] ⊆ [1.25, 6]`. -/
theorem tail_erf (eps : ℚ) (heps : eps * (772 / 10000) < 1 / 2 ^ 53) (X q : UInt64) (hX : Finite X)
    (hx : 5 / 4 ≤ value X) (hqf : Finite q)
    (hq : |value q - RealErf.erfc (value X)| ≤ (eps : ℝ) * RealErf.erfc (value X)) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value X))
      (Wasm.IEEE64.sub 0x3FF0000000000000 q) := by
  set x := value X
  have hey : 0 < RealErf.erfc x := erfc_pos x
  have he54 : RealErf.erfc x ≤ 772 / 10000 :=
    (erfc_strictAnti.antitone hx).trans erfc_five_fourths
  have heps' : (eps : ℝ) * (772 / 10000) < 1 / 2 ^ 53 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr heps
    push_cast at h
    exact h
  have heps0 : (0 : ℝ) ≤ eps := by
    by_contra h
    push_neg at h
    have h1 := abs_nonneg (value q - RealErf.erfc x)
    have h2 := mul_neg_of_neg_of_pos h hey
    linarith only [h1, h2, hq]
  have hqe : |value q - RealErf.erfc x| < 1 / 2 ^ 53 := by
    have : (eps : ℝ) * RealErf.erfc x ≤ eps * (772 / 10000) := mul_le_mul_of_nonneg_left he54 heps0
    linarith
  have hneg := F64NegateOps.finite_negate q hqf
  have hnv : value (Wasm.IEEE64.negate q) = -value q := by
    simp only [value, F64NegateOps.scaledValue_negate, Int.cast_neg, neg_div]
  have hsub : Wasm.IEEE64.sub 0x3FF0000000000000 q =
      Wasm.IEEE64.add 0x3FF0000000000000 (Wasm.IEEE64.negate q) := rfl
  rw [hsub]
  have hql := (abs_lt.mp hqe).1
  have hqu := (abs_lt.mp hqe).2
  have hy : RealErf.erf x = 1 - RealErf.erfc x := by simp [RealErf.erfc]
  have hn := F64NearestSum.add_nearest _ _ ErfTailEval.one_finite hneg (by
    rw [one_value, hnv]
    linarith [show (1 : ℝ) / 2 ^ 53 < 1 / 2 by norm_num]) (by
    rw [one_value, hnv]
    linarith [show (2 : ℝ) ≤ 2 ^ 1023 by norm_num, show (1 : ℝ) / 2 ^ 53 < 1 by norm_num])
  rw [one_value, hnv] at hn
  have hb : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  refine F64AddNearest.within_of_nearest 1 le_rfl (RealErf.erf x) _ _ 1022 (by norm_num) (by norm_num)
    (by rw [hb, hy]; linarith) (by rw [hb]; linarith [show (1 : ℝ) / 2 ^ 53 < 1 / 4 by norm_num])
    ?_ hn ?_
  · have := erf_lt_one x
    have h : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 from rfl]
      norm_num
    linarith
  · have hsp2 : ((1 : Nat) : ℝ) * ((2 : ℝ) ^ (1022 - 1) / (2 : ℝ) ^ 1074) = 1 / 2 ^ 53 := by
      norm_num
    rw [hsp2, hy]
    have : 1 + -value q - (1 - RealErf.erfc x) = -(value q - RealErf.erfc x) := by ring
    rw [this, abs_neg]
    exact hqe

#print axioms x_erfc
#print axioms rel_mul
#print axioms tail_compose
#print axioms erfc_five_fourths
#print axioms tail_erf

end Library.Numerics.Float64.Erf.ErfTailCompose
