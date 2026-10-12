import Verified.Examples.TgammaDD
import Verified.Examples.TgammaFloor
import LeanExe.ProofKit.F64Exact

/-!
The kernel of `Tgamma.asLogd` after the argument reduction.  For doubles `r` and `t` with
`Z = r t - 1` at most `1/2400` in magnitude, the code computes `o = r t` rounded, which is at least
`0.99`, `dxh = o - 1`, which is exact by Sterbenz's lemma, `dxl = fma (r, t, -o)`, which is the
rounding error of `o` up to `2^-104`, and the polynomial term `f = dx² ((c0 + dx c1) + dx² (c2 +
dx c3))` with `dx = fma (r, t, -1)`.  `kernel_spec` bounds `dxh + dxl - Z` by `2^-104` and
`f - Z² P(Z)` by `2^-72`, with `P(Z) = c0 + Z (c1 + Z (c2 + Z c3))`, for coefficients below `1/2`,
`0.34`, `0.26`, and `0.21` in magnitude.  Each step follows the rounded operations through
`F64Approx`.
-/

namespace Verified.Examples.TgammaLogdKernel
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD TgammaFloor

set_option exponentiation.threshold 4096

theorem one_value : value (1.0 : Float).toBits = 1 := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl, ← PolyBound.ratOfWord_cast,
    show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by decide +kernel]
  norm_num

theorem one_finite : Finite (1.0 : Float).toBits := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  unfold CodeLib.IEEE64.Finite; decide

/-- **The kernel of `asLogd`.** -/
theorem kernel_spec (hF : FmaSpec.FmaNearest) (r t c0 c1 c2 c3 : Float)
    (hr : Finite r.toBits) (ht : Finite t.toBits) (hc0 : Finite c0.toBits)
    (hc1 : Finite c1.toBits) (hc2 : Finite c2.toBits) (hc3 : Finite c3.toBits)
    (hz : |value r.toBits * value t.toBits - 1| ≤ 1 / 2400)
    (hb0 : |value c0.toBits| ≤ 1 / 2) (hb1 : |value c1.toBits| ≤ 34 / 100)
    (hb2 : |value c2.toBits| ≤ 26 / 100) (hb3 : |value c3.toBits| ≤ 21 / 100) :
    Finite (r * t).toBits ∧ 99 / 100 ≤ value (r * t).toBits ∧
      value (r * t - 1.0).toBits = value (r * t).toBits - 1 ∧
      Finite (r * t - 1.0).toBits ∧ Finite (Fma.fma r t (-(r * t))).toBits ∧
      Finite ((Fma.fma r t (-1.0) * Fma.fma r t (-1.0)) *
        ((c0 + Fma.fma r t (-1.0) * c1) +
          (Fma.fma r t (-1.0) * Fma.fma r t (-1.0)) * (c2 + Fma.fma r t (-1.0) * c3))).toBits ∧
      |value (r * t - 1.0).toBits + value (Fma.fma r t (-(r * t))).toBits -
          (value r.toBits * value t.toBits - 1)| ≤ 1 / 2 ^ 104 ∧
      |value (r * t - 1.0).toBits| ≤ 1 / 2400 + 1 / 2 ^ 52 ∧
      |value (Fma.fma r t (-(r * t))).toBits| ≤ 1 / 2 ^ 52 ∧
      |value ((Fma.fma r t (-1.0) * Fma.fma r t (-1.0)) *
          ((c0 + Fma.fma r t (-1.0) * c1) +
            (Fma.fma r t (-1.0) * Fma.fma r t (-1.0)) * (c2 + Fma.fma r t (-1.0) * c3))).toBits -
        (value r.toBits * value t.toBits - 1) ^ 2 *
          (value c0.toBits + (value r.toBits * value t.toBits - 1) * (value c1.toBits +
            (value r.toBits * value t.toBits - 1) * (value c2.toBits +
              (value r.toBits * value t.toBits - 1) * value c3.toBits)))| ≤ 1 / 2 ^ 72 ∧
      |value ((Fma.fma r t (-1.0) * Fma.fma r t (-1.0)) *
        ((c0 + Fma.fma r t (-1.0) * c1) +
          (Fma.fma r t (-1.0) * Fma.fma r t (-1.0)) * (c2 + Fma.fma r t (-1.0) * c3))).toBits| ≤
        1 / 2 ^ 23 := by
  set ρ := value r.toBits with hρ
  set τ := value t.toBits with hτ
  set Z := ρ * τ - 1 with hZ
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  have hP : 0 < ρ * τ := by linarith
  -- `o`, `dxh`, `dxl`
  have ho := fapprox_mul (fapprox_self r hr) (fapprox_self t ht) |ρ| |τ| le_rfl le_rfl
    (|ρ| * |τ|) (by simp) (by rw [← abs_mul]; rw [abs_of_pos hP]; linarith)
  simp only [mul_zero, zero_mul, add_zero, zero_add] at ho
  rw [← abs_mul, abs_of_pos hP] at ho
  set o := r * t with hodef
  have ho2 := abs_le.mp ho.2
  have hop : 0.99 < value o.toBits := by
    linarith [(by norm_num : (1 : ℝ) - 1 / 2400 - (1 + 1 / 2400) / 2 ^ 53 - 1 / 2 ^ 1075 > 0.99)]
  have hoq : value o.toBits < 1.01 := by
    linarith [(by norm_num : (1 : ℝ) + 1 / 2400 + (1 + 1 / 2400) / 2 ^ 53 + 1 / 2 ^ 1075 < 1.01)]
  have hsub := F64Exact.sub_exact o.toBits (1.0 : Float).toBits ho.1 one_finite (by linarith)
    (by rw [one_value]; norm_num) (by rw [one_value]; linarith) (by rw [one_value]; linarith)
    (by linarith [(by norm_num : (1.01 : ℝ) < 2 ^ 900)]) (by rw [one_value]; norm_num)
  rw [← F64Bits.toBits_sub, one_value] at hsub
  obtain ⟨hnf, hnv⟩ := neg_float o ho.1
  have hl := fma_approx hF r t (-o) hr ht hnf (by
    rw [hnv]; have := abs_sub_comm (ρ * τ) (value o.toBits)
    rw [← sub_eq_add_neg]; linarith [abs_nonneg (ρ * τ - value o.toBits), ho.2,
      (by norm_num : (1 + 1 / 2400 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)])
  rw [hnv, ← sub_eq_add_neg] at hl
  have hro : |ρ * τ - value o.toBits| ≤ (1 + 1 / 2400) / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_sub_comm]; linarith [ho.2]
  have hl2 := hl.2
  have hlb : |ρ * τ - value o.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 104 := by
    have : |ρ * τ - value o.toBits| / 2 ^ 53 ≤ ((1 + 1 / 2400) / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 :=
      div_le_div_of_nonneg_right hro (by positivity)
    linarith [(by norm_num : ((1 + 1 / 2400 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 +
      1 / 2 ^ 1075 ≤ 1 / 2 ^ 104)]
  -- `dx` and the polynomial
  have hdx := fma_approx hF r t (-1.0) hr ht (neg_float _ one_finite).1 (by
    rw [(neg_float _ one_finite).2, one_value, ← sub_eq_add_neg]; linarith [hz])
  rw [(neg_float _ one_finite).2, one_value, ← sub_eq_add_neg] at hdx
  have hdx' : FApprox (Fma.fma r t (-1.0)) Z (1 / 2 ^ 64) := hdx.mono (by
    have : |Z| / 2 ^ 53 ≤ (1 / 2400) / 2 ^ 53 := div_le_div_of_nonneg_right hz (by positivity)
    linarith [(by norm_num : (1 / 2400 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 64)])
  set dx := Fma.fma r t (-1.0) with hdxdef
  have hA1 := (fapprox_mul hdx' (fapprox_self c1 hc1) (1 / 2400) (34 / 100) hz hb1 (1 / 7000)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 64 : ℝ) by norm_num)
  have hA2 := (fapprox_add (fapprox_self c0 hc0) hA1 (5002 / 10000) (by
    have : |value c0.toBits + Z * value c1.toBits| ≤ 1 / 2 + 1 / 2400 * (34 / 100) := by
      have h1 := abs_add_le (value c0.toBits) (Z * value c1.toBits)
      rw [abs_mul] at h1
      nlinarith [abs_nonneg Z, abs_nonneg (value c1.toBits)]
    linarith [(by norm_num : (1 / 2 + 1 / 2400 * (34 / 100) : ℝ) + (0 + 1 / 2 ^ 64) ≤
      5002 / 10000)]) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 53 : ℝ) by norm_num)
  have hB1 := (fapprox_mul hdx' (fapprox_self c3 hc3) (1 / 2400) (21 / 100) hz hb3 (1 / 11000)
    (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 64 : ℝ) by norm_num)
  have hB2 := (fapprox_add (fapprox_self c2 hc2) hB1 (2601 / 10000) (by
    have : |value c2.toBits + Z * value c3.toBits| ≤ 26 / 100 + 1 / 2400 * (21 / 100) := by
      have h1 := abs_add_le (value c2.toBits) (Z * value c3.toBits)
      rw [abs_mul] at h1
      nlinarith [abs_nonneg Z, abs_nonneg (value c3.toBits)]
    linarith [(by norm_num : (26 / 100 + 1 / 2400 * (21 / 100) : ℝ) + (0 + 1 / 2 ^ 64) ≤
      2601 / 10000)]) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 54 : ℝ) by norm_num)
  have hZ2 : |Z| ≤ 1 / 2400 := hz
  have hD := (fapprox_mul hdx' hdx' (1 / 2400) (1 / 2400) hZ2 hZ2 (1 / 5700000) (by norm_num)
    (by norm_num)).mono (show _ ≤ (65 / 10 ^ 24 : ℝ) by norm_num)
  have hZsq : |Z * Z| ≤ 1 / 2400 * (1 / 2400) := by
    rw [abs_mul]; exact mul_le_mul hz hz (abs_nonneg _) (by norm_num)
  have hB2v : |value c2.toBits + Z * value c3.toBits| ≤ 2601 / 10000 := by
    have h1 := abs_add_le (value c2.toBits) (Z * value c3.toBits)
    rw [abs_mul] at h1
    nlinarith [abs_nonneg Z, abs_nonneg (value c3.toBits)]
  have hC1 := (fapprox_mul hD hB2 (1 / 2400 * (1 / 2400)) (2601 / 10000) hZsq hB2v
    (1 / 22000000) (by norm_num) (by norm_num)).mono (show _ ≤ (43 / 10 ^ 24 : ℝ) by norm_num)
  have hPv : |value c0.toBits + Z * value c1.toBits +
      Z * Z * (value c2.toBits + Z * value c3.toBits)| ≤ 5002 / 10000 := by
    have h1 := abs_add_le (value c0.toBits + Z * value c1.toBits)
      (Z * Z * (value c2.toBits + Z * value c3.toBits))
    have h2 := abs_add_le (value c0.toBits) (Z * value c1.toBits)
    rw [abs_mul (Z * Z)] at h1
    rw [abs_mul] at h2
    have h3 : |Z * Z| * |value c2.toBits + Z * value c3.toBits| ≤
        1 / 2400 * (1 / 2400) * (2601 / 10000) :=
      mul_le_mul hZsq hB2v (abs_nonneg _) (by norm_num)
    have h4 : |Z| * |value c1.toBits| ≤ 1 / 2400 * (34 / 100) :=
      mul_le_mul hz hb1 (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (1 / 2 + 1 / 2400 * (34 / 100) + 1 / 2400 * (1 / 2400) * (2601 / 10000)
      : ℝ) ≤ 5002 / 10000)]
  have hC2 := (fapprox_add hA2 hC1 (5003 / 10000) (by
    linarith [(by norm_num : (5002 / 10000 : ℝ) + (1 / 2 ^ 53 + 43 / 10 ^ 24) ≤ 5003 / 10000)])
    (by norm_num)).mono (show _ ≤ (17 / 10 ^ 17 : ℝ) by norm_num)
  have hF' := (fapprox_mul hD hC2 (1 / 2400 * (1 / 2400)) (5002 / 10000) hZsq hPv
    (1 / 11500000) (by norm_num) (by norm_num)).mono (show _ ≤ (1 / 2 ^ 72 : ℝ) by norm_num)
  refine ⟨ho.1, by linarith, hsub.2, hsub.1, hl.1, hF'.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsub.2]
    have : value o.toBits - 1 + value (Fma.fma r t (-o)).toBits - Z =
        value (Fma.fma r t (-o)).toBits - (ρ * τ - value o.toBits) := by rw [hZ]; ring
    rw [this]; linarith
  · rw [hsub.2]
    rw [abs_le]; constructor <;> linarith [(by norm_num : (1 + 1 / 2400 : ℝ) / 2 ^ 53 +
      1 / 2 ^ 1075 ≤ 1 / 2 ^ 52)]
  · have h1 := abs_sub_abs_le_abs_sub (value (Fma.fma r t (-o)).toBits) (ρ * τ - value o.toBits)
    linarith [(by norm_num : (1 + 1 / 2400 : ℝ) / 2 ^ 53 + 1 / 2 ^ 1075 + 1 / 2 ^ 104 ≤
      1 / 2 ^ 52)]
  · have h2 := hF'.2
    have : Z * Z * (value c0.toBits + Z * value c1.toBits +
        Z * Z * (value c2.toBits + Z * value c3.toBits)) = Z ^ 2 * (value c0.toBits +
        Z * (value c1.toBits + Z * (value c2.toBits + Z * value c3.toBits))) := by ring
    rw [this] at h2
    exact h2
  · have h2 := hF'.2
    have h3 := abs_sub_abs_le_abs_sub (value ((dx * dx) * ((c0 + dx * c1) +
      (dx * dx) * (c2 + dx * c3))).toBits) (Z * Z * (value c0.toBits + Z * value c1.toBits +
        Z * Z * (value c2.toBits + Z * value c3.toBits)))
    have h4 : |Z * Z * (value c0.toBits + Z * value c1.toBits +
        Z * Z * (value c2.toBits + Z * value c3.toBits))| ≤ 1 / 2400 * (1 / 2400) * (5002 / 10000) := by
      rw [abs_mul]; exact mul_le_mul hZsq hPv (abs_nonneg _) (by norm_num)
    linarith [(by norm_num : (1 / 2400 * (1 / 2400) * (5002 / 10000) : ℝ) + 1 / 2 ^ 72 ≤
      1 / 2 ^ 23)]

#print axioms kernel_spec

end Verified.Examples.TgammaLogdKernel
