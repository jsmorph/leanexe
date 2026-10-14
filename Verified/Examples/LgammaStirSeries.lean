import Verified.Examples.LgammaFastMid
import Verified.Examples.LgammaRecip
import Verified.Examples.TgammaMul

/-!
The term `S (1/x²)/x` of the fast path's Stirling series in `Lgamma.lgammaWith`, for `x` from
`33/4` to `2 ^ 100`.  The code computes `zh + zl ≈ 1/x` (`LgammaRecip.recip_big`), the tail
`F = w (c401 + c402 w + w² (c403 + c404 w + w² c405))` at `w = zh zh` in plain double arithmetic
(`sE`, bounded by `TgammaExpr`), the exact sum `c399 + F` (`fastTwoSum`), and the product with
`zh + zl` (`mulDD`).  `w` differs from `1/x²` by about `2 ^ -51` of `1/x²`, which the Lipschitz
bound `sE_lip` carries to the tail, and the result lies within `2 ^ -66` of
`(c399 + c400 + evalR sE (1/x²))/x` (`series_spec`).
-/

namespace Verified.Examples.LgammaStirSeries
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPolyDDD TgammaExpr TgammaWords
  LgammaPiecePoly LgammaFastSmall

set_option exponentiation.threshold 4096

/-- The tail of the series in `w = 1/x²`. -/
def sE : FE :=
  .mul .var (.add (lin (wq 401) (wq 402))
    (.mul (.mul .var .var) (.add (lin (wq 403) (wq 404)) (.mul (.mul .var .var) (.const (wq 405))))))

theorem sE_ok : ok sE (1 / 64) = true := by decide +kernel

theorem sE_bnd : (bnd sE (1 / 64)).1 ≤ 1 / 2 ^ 14 ∧ (bnd sE (1 / 64)).2 ≤ 1 / 2 ^ 65 := by
  decide +kernel

/-- The words of the series. -/
theorem coef_ok : (∀ i < 9, Wasm.IEEE64.isFinite (wq (397 + i)) = true) ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 401)) ≤ 3 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 402)) ≤ 1 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 403)) ≤ 1 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 404)) ≤ 1 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 405)) ≤ 1 / 500 ∧
    83 / 1000 ≤ PolyBound.ratOfWord (wq 399) ∧ PolyBound.ratOfWord (wq 399) ≤ 84 / 1000 ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 400)) ≤ 1 / 2 ^ 58 ∧
    41 / 100 ≤ PolyBound.ratOfWord (wq 397) ∧ PolyBound.ratOfWord (wq 397) ≤ 42 / 100 ∧
    PolyBound.qabs (PolyBound.ratOfWord (wq 398)) ≤ 1 / 2 ^ 57 := by
  decide +kernel

/-- `|a ^ i b ^ j| ≤ X ^ (i + j)` for `|a|, |b| ≤ X`. -/
theorem mono_le (a b X : ℝ) (ha : |a| ≤ X) (hb : |b| ≤ X) (i j : ℕ) :
    |a ^ i * b ^ j| ≤ X ^ (i + j) := by
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha i) (pow_le_pow_left₀ (abs_nonneg _) hb j)
    (by positivity) (le_trans (by positivity) (pow_le_pow_left₀ (abs_nonneg _) ha i))

/-- **The Lipschitz bound** of the tail on `|w| ≤ 1/64`. -/
theorem sE_lip (a b : ℝ) (ha : |a| ≤ 1 / 64) (hb : |b| ≤ 1 / 64) :
    |evalR sE a - evalR sE b| ≤ |a - b| / 256 := by
  obtain ⟨-, h1, h2, h3, h4, h5, -⟩ := coef_ok
  set c1 : ℝ := (PolyBound.ratOfWord (wq 401) : ℝ)
  set c2 : ℝ := (PolyBound.ratOfWord (wq 402) : ℝ)
  set c3 : ℝ := (PolyBound.ratOfWord (wq 403) : ℝ)
  set c4 : ℝ := (PolyBound.ratOfWord (wq 404) : ℝ)
  set c5 : ℝ := (PolyBound.ratOfWord (wq 405) : ℝ)
  have hc (q : ℚ) (B : ℚ) (h : PolyBound.qabs q ≤ B) : |(q : ℝ)| ≤ (B : ℝ) := abs_rat_le q B h
  have hc1 := hc _ _ h1
  have hc2 := hc _ _ h2
  have hc3 := hc _ _ h3
  have hc4 := hc _ _ h4
  have hc5 := hc _ _ h5
  push_cast at hc1 hc2 hc3 hc4 hc5
  have hid : evalR sE a - evalR sE b = (a - b) *
      (c1 + c2 * (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1) +
        c3 * (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2) +
        c4 * (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3) +
        c5 * (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3 + a ^ 0 * b ^ 4)) := by
    simp only [evalR, sE, lin]
    ring
  rw [hid, abs_mul]
  have hX := mono_le a b (1 / 64) ha hb
  have m10 := hX 1 0
  have m01 := hX 0 1
  have m20 := hX 2 0
  have m11 := hX 1 1
  have m02 := hX 0 2
  have m30 := hX 3 0
  have m21 := hX 2 1
  have m12 := hX 1 2
  have m03 := hX 0 3
  have m40 := hX 4 0
  have m31 := hX 3 1
  have m22 := hX 2 2
  have m13 := hX 1 3
  have m04 := hX 0 4
  norm_num at m10 m01 m20 m11 m02 m30 m21 m12 m03 m40 m31 m22 m13 m04
  have t2 : |a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1| ≤ 2 / 64 := by
    have := abs_add_le (a ^ 1 * b ^ 0) (a ^ 0 * b ^ 1)
    norm_num at this ⊢
    linarith
  have t3 : |a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2| ≤ 3 / 64 ^ 2 := by
    have := abs_add_three (a ^ 2 * b ^ 0) (a ^ 1 * b ^ 1) (a ^ 0 * b ^ 2)
    norm_num at this ⊢
    linarith
  have t4 : |a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3| ≤ 4 / 64 ^ 3 := by
    have e1 := abs_add_le (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2) (a ^ 0 * b ^ 3)
    have e2 := abs_add_three (a ^ 3 * b ^ 0) (a ^ 2 * b ^ 1) (a ^ 1 * b ^ 2)
    norm_num at e1 e2 ⊢
    linarith
  have t5 : |a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3 + a ^ 0 * b ^ 4| ≤
      5 / 64 ^ 4 := by
    have e1 := abs_add_le (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3) (a ^ 0 * b ^ 4)
    have e2 := abs_add_le (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2) (a ^ 1 * b ^ 3)
    have e3 := abs_add_three (a ^ 4 * b ^ 0) (a ^ 3 * b ^ 1) (a ^ 2 * b ^ 2)
    norm_num at e1 e2 e3 ⊢
    linarith
  have hK : |c1 + c2 * (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1) +
        c3 * (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2) +
        c4 * (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3) +
        c5 * (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3 + a ^ 0 * b ^ 4)| ≤
      1 / 256 := by
    have p2 := abs_mul c2 (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1)
    have p3 := abs_mul c3 (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2)
    have p4 := abs_mul c4 (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3)
    have p5 := abs_mul c5
      (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3 + a ^ 0 * b ^ 4)
    have q2 := mul_le_mul hc2 t2 (abs_nonneg _) (by norm_num)
    have q3 := mul_le_mul hc3 t3 (abs_nonneg _) (by norm_num)
    have q4 := mul_le_mul hc4 t4 (abs_nonneg _) (by norm_num)
    have q5 := mul_le_mul hc5 t5 (abs_nonneg _) (by norm_num)
    have s1 := abs_add_le (c1 + c2 * (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1) +
        c3 * (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2) +
        c4 * (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3))
      (c5 * (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3 + a ^ 0 * b ^ 4))
    have s2 := abs_add_le (c1 + c2 * (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1) +
        c3 * (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2))
      (c4 * (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3))
    have s3 := abs_add_three c1 (c2 * (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1))
      (c3 * (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2))
    linarith
  calc |a - b| * |c1 + c2 * (a ^ 1 * b ^ 0 + a ^ 0 * b ^ 1) +
        c3 * (a ^ 2 * b ^ 0 + a ^ 1 * b ^ 1 + a ^ 0 * b ^ 2) +
        c4 * (a ^ 3 * b ^ 0 + a ^ 2 * b ^ 1 + a ^ 1 * b ^ 2 + a ^ 0 * b ^ 3) +
        c5 * (a ^ 4 * b ^ 0 + a ^ 3 * b ^ 1 + a ^ 2 * b ^ 2 + a ^ 1 * b ^ 3 + a ^ 0 * b ^ 4)|
      ≤ |a - b| * (1 / 256) := mul_le_mul_of_nonneg_left hK (abs_nonneg _)
    _ = |a - b| / 256 := by ring

set_option maxHeartbeats 1000000 in
/-- **The `1/x` term** of the fast path's Stirling series, within `2 ^ -65` of
`(c399 + c400 + evalR sE (1/x²))/x`, for `x` from `33/4` to `2 ^ 100`. -/
theorem series_spec (hF : FmaSpec.FmaNearest) (ax : Float) (hax : Finite ax.toBits)
    (h1 : 33 / 4 ≤ value ax.toBits) (h2 : value ax.toBits ≤ 2 ^ 100) (D T : Float × Float)
    (hD : D = fastTwoSum (entry Lgamma.mainTable 399) (evalF sE ((1.0 / ax) * (1.0 / ax))))
    (hT : T = mulDD D.1 (D.2 + entry Lgamma.mainTable 400) (1.0 / ax)
      (Fma.fma (1.0 / ax) (-ax) 1.0 * (1.0 / ax))) :
    Finite T.1.toBits ∧ Finite T.2.toBits ∧
      |value T.1.toBits + value T.2.toBits -
          ((((PolyBound.ratOfWord (wq 399) + PolyBound.ratOfWord (wq 400) : ℚ)) : ℝ) +
            evalR sE ((1 / value ax.toBits) ^ 2)) * (1 / value ax.toBits)| ≤ 1 / 2 ^ 65 ∧
      |value T.1.toBits| ≤ 1 / 64 ∧ |value T.2.toBits| ≤ 1 / 2 ^ 50 := by
  obtain ⟨hfin, -, -, -, -, -, h399a, h399b, h400, -, -, -⟩ := coef_ok
  have hv0 : 0 < value ax.toBits := by linarith
  obtain ⟨hzf, hzlf, hz1, hzl, hz2⟩ := LgammaRecip.recip_big hF ax hax
    (by rw [abs_of_pos hv0]; linarith) (by rw [abs_of_pos hv0]; exact h2)
  rw [abs_of_pos (show (0 : ℝ) < 1 / value ax.toBits by positivity)] at hz1 hzl hz2
  set R := 1 / value ax.toBits with hRdef
  have hR0 : 0 < R := by positivity
  have hR1 : R ≤ 4 / 33 := by
    rw [hRdef, div_le_div_iff₀ hv0 (by norm_num)]; linarith
  set zh := 1.0 / ax with hzhdef
  set zl := Fma.fma zh (-ax) 1.0 * zh with hzldef
  set vz := value zh.toBits with hvzdef
  set vzl := value zl.toBits with hvzldef
  have hzhb : |vz| ≤ R * (1 + 1 / 2 ^ 52) := by
    have := abs_sub_abs_le_abs_sub vz R
    rw [abs_of_pos hR0] at this
    linarith
  -- `w = zh zh` near `R ^ 2`
  have hsq := fapprox_mul (fapprox_self zh hzf) (fapprox_self zh hzf) (R * (1 + 1 / 2 ^ 52))
    (R * (1 + 1 / 2 ^ 52)) hzhb hzhb ((R * (1 + 1 / 2 ^ 52) + 0) * (R * (1 + 1 / 2 ^ 52) + 0))
    le_rfl (by nlinarith)
  set w := zh * zh with hwdef
  set vw := value w.toBits with hvwdef
  have hw1 : |vw - vz * vz| ≤ (R * (1 + 1 / 2 ^ 52)) * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 53 +
      1 / 2 ^ 1075 := by
    have := hsq.2
    simp only [zero_mul, mul_zero, add_zero, zero_add] at this
    exact this
  have hvz2 : |vz * vz - R * R| ≤ R * R / 2 ^ 50 := by
    rw [show vz * vz - R * R = (vz - R) * (vz + R) by ring, abs_mul]
    have h3 : |vz + R| ≤ 3 * R := by
      have := abs_add_le (vz - R) (2 * R)
      rw [show vz - R + 2 * R = vz + R by ring, abs_of_pos (by positivity : (0 : ℝ) < 2 * R)] at this
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 ≤ 1)]
    calc |vz - R| * |vz + R| ≤ R / 2 ^ 52 * (3 * R) := mul_le_mul hz1 h3 (abs_nonneg _) (by positivity)
      _ ≤ R * R / 2 ^ 50 := by
        have : (0 : ℝ) ≤ R * R := by positivity
        rw [show R / 2 ^ 52 * (3 * R) = R * R * (3 / 2 ^ 52) by ring,
          show R * R / 2 ^ 50 = R * R * (1 / 2 ^ 50) by ring]
        exact mul_le_mul_of_nonneg_left (by norm_num) this
  have hRR : R * R ≤ 16 / 1089 := by nlinarith
  have hwR : |vw - R ^ 2| ≤ R * R / 2 ^ 49 + 1 / 2 ^ 1075 := by
    have h4 : (R * (1 + 1 / 2 ^ 52)) * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 53 ≤ R * R / 2 ^ 52 := by
      rw [show (R * (1 + 1 / 2 ^ 52)) * (R * (1 + 1 / 2 ^ 52)) / 2 ^ 53 =
        R * R * ((1 + 1 / 2 ^ 52) ^ 2 / 2 ^ 53) by ring, show R * R / 2 ^ 52 = R * R * (1 / 2 ^ 52) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    have := abs_sub_le vw (vz * vz) (R ^ 2)
    rw [show R ^ 2 = R * R by ring] at this ⊢
    have h5 : R * R / 2 ^ 50 + R * R / 2 ^ 52 ≤ R * R / 2 ^ 49 := by
      rw [show R * R / 2 ^ 50 + R * R / 2 ^ 52 = R * R * (1 / 2 ^ 50 + 1 / 2 ^ 52) by ring,
        show R * R / 2 ^ 49 = R * R * (1 / 2 ^ 49) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    linarith
  have hwb : |vw| ≤ 1 / 64 := by
    have h1' := abs_sub_abs_le_abs_sub vw (R ^ 2)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R ^ 2)] at h1'
    have h2' : R * R / 2 ^ 49 ≤ 16 / 1089 / 2 ^ 49 := div_le_div_of_nonneg_right hRR (by norm_num)
    have h3' : R ^ 2 = R * R := by ring
    linarith [(by norm_num : (16 : ℝ) / 1089 + 16 / 1089 / 2 ^ 49 + 1 / 2 ^ 1075 ≤ 1 / 64)]
  -- the tail `F`
  have hwX : |value w.toBits| ≤ ((1 / 64 : ℚ) : ℝ) := by push_cast; exact hwb
  obtain ⟨hFa, hFm⟩ := evalF_approx sE (1 / 64) w hsq.1 hwX sE_ok
  have hb1 := qcast_le sE_bnd.1
  have hb2 := qcast_le sE_bnd.2
  push_cast at hb1 hb2
  set F := evalF sE w with hFdef
  set vF := value F.toBits with hvFdef
  have hFe : |vF - evalR sE vw| ≤ 1 / 2 ^ 65 := hFa.2.trans hb2
  have hFb : |vF| ≤ 1 / 2 ^ 13 := by
    have := abs_sub_abs_le_abs_sub vF (evalR sE vw)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 14 + 1 / 2 ^ 65 ≤ 1 / 2 ^ 13)]
  have hlip := sE_lip vw (R ^ 2) hwb (by
    rw [abs_of_nonneg (by positivity), show R ^ 2 = R * R by ring]
    linarith [(by norm_num : (16 : ℝ) / 1089 ≤ 1 / 64)])
  -- `c399 + F`, exact
  have he399 : entry Lgamma.mainTable 399 = Float.ofBits (wq 399) := rfl
  have he400 : entry Lgamma.mainTable 400 = Float.ofBits (wq 400) := rfl
  have hf399 := ofBits_finite _ (hfin 2 (by norm_num))
  have hf400 := ofBits_finite _ (hfin 3 (by norm_num))
  have hv399 := ofBits_value _ (hfin 2 (by norm_num))
  have hv400 := ofBits_value _ (hfin 3 (by norm_num))
  have hc399a := qcast_le h399a
  have hc399b := qcast_le h399b
  have hc400 := abs_rat_le _ _ h400
  push_cast at hc399a hc399b hc400
  rw [he399] at hD
  rw [he400] at hT
  obtain ⟨hD1f, hD2f, hDs, hD2a, hD2b⟩ := fastTwoSum_spec (Float.ofBits (wq 399)) F hf399 hFa.1
    (by
      rw [hv399, abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ) by linarith)]
      linarith)
    (by
      rw [hv399, abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ) by linarith)]
      linarith)
  rw [← hD] at hD1f hD2f hDs hD2a hD2b
  rw [hv399] at hDs
  have hD1b : |value D.1.toBits| ≤ 85 / 1000 := by
    have h1' := abs_sub_abs_le_abs_sub (value D.1.toBits) (-value D.2.toBits)
    rw [sub_neg_eq_add, abs_neg, hDs] at h1'
    have := abs_add_le ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ) vF
    rw [abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ) by linarith)] at this
    linarith [(by norm_num : (84 : ℝ) / 1000 + 1 / 2 ^ 13 + 1 / 2 ^ 13 ≤ 85 / 1000)]
  have hD2c : |value D.2.toBits| ≤ 1 / 2 ^ 55 := by
    have : |value D.1.toBits| / 2 ^ 52 ≤ 85 / 1000 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hD1b (by norm_num)
    linarith [(by norm_num : (85 : ℝ) / 1000 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 55)]
  -- `D.2 + c400`
  have hx' := fapprox_add (fapprox_self D.2 hD2f) (fapprox_self _ hf400) (1 / 2 ^ 54)
    (by
      rw [hv400]
      have := abs_add_le (value D.2.toBits) ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 55 + 1 / 2 ^ 58 ≤ 1 / 2 ^ 54)])
    (by norm_num)
  rw [hv400] at hx'
  set x' := D.2 + Float.ofBits (wq 400) with hx'def
  have hx'e : |value x'.toBits - (value D.2.toBits + ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ))| ≤
      1 / 2 ^ 107 := by
    have := hx'.2
    norm_num at this ⊢
    linarith
  have hx'b : |value x'.toBits| ≤ 1 / 2 ^ 54 := by
    have h1' := abs_sub_abs_le_abs_sub (value x'.toBits)
      (value D.2.toBits + ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ))
    have := abs_add_le (value D.2.toBits) ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 107 + 1 / 2 ^ 55 + 1 / 2 ^ 58 ≤ 1 / 2 ^ 54)]
  -- the product
  have hzlb : |vzl| ≤ R / 2 ^ 50 := hzl
  have hH : |vz| * |value D.1.toBits| ≤ R * (1 + 1 / 2 ^ 52) * (85 / 1000) :=
    mul_le_mul hzhb hD1b (abs_nonneg _) (by positivity)
  have hP1 : |vz| * |value x'.toBits| ≤ R * (1 + 1 / 2 ^ 52) * (1 / 2 ^ 54) :=
    mul_le_mul hzhb hx'b (abs_nonneg _) (by positivity)
  have hP2 : |vzl| * |value D.1.toBits| ≤ R / 2 ^ 50 * (85 / 1000) :=
    mul_le_mul hzlb hD1b (abs_nonneg _) (by positivity)
  have hL2 : |vzl| * |value x'.toBits| ≤ R / 2 ^ 50 * (1 / 2 ^ 54) :=
    mul_le_mul hzlb hx'b (abs_nonneg _) (by positivity)
  obtain ⟨hT1, hT2, hTe, hT2b, hT1b⟩ := TgammaMul.mulDD_spec hF D.1 x' zh zl hD1f hx'.1 hzf hzlf
    _ _ _ _ hH hP1 hP2 hL2 (by nlinarith) (by nlinarith)
  rw [← hT] at hT1 hT2 hTe hT2b hT1b
  refine ⟨hT1, hT2, ?_, ?_, ?_⟩
  · -- the error
    set c := ((PolyBound.ratOfWord (wq 399) + PolyBound.ratOfWord (wq 400) : ℚ) : ℝ) with hcdef
    have hc : c = ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ) + ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ) := by
      rw [hcdef]; push_cast; ring
    -- `(D.1 + x') (zh + zl) - (c + vF) R`
    have hS1 : value D.1.toBits + value x'.toBits = c + vF +
        (value x'.toBits - (value D.2.toBits + ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ))) := by
      rw [hc]; linarith
    have hE2 : |(value D.1.toBits + value x'.toBits) * (vz + vzl) - (c + vF) * R| ≤ 1 / 2 ^ 100 := by
      rw [hS1]
      set d := value x'.toBits - (value D.2.toBits + ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ))
      have hcF : |c + vF| ≤ 85 / 1000 := by
        rw [hc]
        have := abs_add_three ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ)
          ((PolyBound.ratOfWord (wq 400) : ℚ) : ℝ) vF
        rw [abs_of_pos (show (0 : ℝ) < ((PolyBound.ratOfWord (wq 399) : ℚ) : ℝ) by linarith)] at this
        linarith [(by norm_num : (84 : ℝ) / 1000 + 1 / 2 ^ 58 + 1 / 2 ^ 13 ≤ 85 / 1000)]
      rw [show (c + vF + d) * (vz + vzl) - (c + vF) * R = (c + vF + d) * (vz + vzl - R) + d * R by ring]
      have e1 : |(c + vF + d) * (vz + vzl - R)| ≤ (85 / 1000 + 1 / 2 ^ 107) * (R / 2 ^ 100) := by
        rw [abs_mul]
        exact mul_le_mul (by linarith [abs_add_le (c + vF) d]) hz2 (abs_nonneg _) (by positivity)
      have e2 : |d * R| ≤ 1 / 2 ^ 107 * (4 / 33) := by
        rw [abs_mul, abs_of_pos hR0]
        exact mul_le_mul hx'e hR1 hR0.le (by norm_num)
      have e3 : (85 / 1000 + 1 / 2 ^ 107) * (R / 2 ^ 100) ≤ (85 / 1000 + 1 / 2 ^ 107) * (4 / 33 / 2 ^ 100) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hR1 (by norm_num)) (by positivity)
      have := abs_add_le ((c + vF + d) * (vz + vzl - R)) (d * R)
      linarith [(by norm_num : ((85 : ℝ) / 1000 + 1 / 2 ^ 107) * (4 / 33 / 2 ^ 100) +
        1 / 2 ^ 107 * (4 / 33) ≤ 1 / 2 ^ 100)]
    -- `(vF - evalR sE (R ^ 2)) R`
    have hE3 : |(c + vF) * R - (c + evalR sE (R ^ 2)) * R| ≤ 1 / 2 ^ 65 - 1 / 2 ^ 99 := by
      rw [show (c + vF) * R - (c + evalR sE (R ^ 2)) * R = (vF - evalR sE (R ^ 2)) * R by ring,
        abs_mul, abs_of_pos hR0]
      have h1' : |vF - evalR sE (R ^ 2)| ≤ 1 / 2 ^ 65 + (R * R / 2 ^ 49 + 1 / 2 ^ 1075) / 256 := by
        have := abs_sub_le vF (evalR sE vw) (evalR sE (R ^ 2))
        have : |vw - R ^ 2| / 256 ≤ (R * R / 2 ^ 49 + 1 / 2 ^ 1075) / 256 :=
          div_le_div_of_nonneg_right hwR (by norm_num)
        linarith
      have h2' : 1 / 2 ^ 65 + (R * R / 2 ^ 49 + 1 / 2 ^ 1075) / 256 ≤
          1 / 2 ^ 65 + (16 / 1089 / 2 ^ 49 + 1 / 2 ^ 1075) / 256 := by
        have : R * R / 2 ^ 49 ≤ 16 / 1089 / 2 ^ 49 := div_le_div_of_nonneg_right hRR (by norm_num)
        linarith
      calc |vF - evalR sE (R ^ 2)| * R ≤
          (1 / 2 ^ 65 + (16 / 1089 / 2 ^ 49 + 1 / 2 ^ 1075) / 256) * (4 / 33) :=
            mul_le_mul (h1'.trans h2') hR1 hR0.le (by positivity)
        _ ≤ 1 / 2 ^ 65 - 1 / 2 ^ 99 := by norm_num
    have hE1 : |value T.1.toBits + value T.2.toBits -
        (value D.1.toBits + value x'.toBits) * (vz + vzl)| ≤ 1 / 2 ^ 100 := by
      refine hTe.trans ?_
      have : R ≤ 4 / 33 := hR1
      nlinarith
    have := abs_sub_le (value T.1.toBits + value T.2.toBits)
      ((value D.1.toBits + value x'.toBits) * (vz + vzl)) ((c + vF) * R)
    have := abs_sub_le (value T.1.toBits + value T.2.toBits) ((c + vF) * R)
      ((c + evalR sE (R ^ 2)) * R)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 100 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 99)]
  · have : R * (1 + 1 / 2 ^ 52) * (85 / 1000) * (1 + 1 / 2 ^ 53) ≤
        4 / 33 * (1 + 1 / 2 ^ 52) * (85 / 1000) * (1 + 1 / 2 ^ 53) := by
      gcongr
    linarith [(by norm_num : (4 : ℝ) / 33 * (1 + 1 / 2 ^ 52) * (85 / 1000) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ 1 / 64)]
  · have : R ≤ 4 / 33 := hR1
    nlinarith

#print axioms sE_lip
#print axioms series_spec

end Verified.Examples.LgammaStirSeries
