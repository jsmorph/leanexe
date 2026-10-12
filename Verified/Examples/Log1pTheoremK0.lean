import Verified.Examples.Log1pTheoremCore
import Verified.Examples.Log1pTheoremConst
import LeanExe.ProofKit.F64RoundNearest

/-!
`Log1p.log1pTail x 0 0 1 = x - (x²/2 - P)` within one step of `log (1 + x)` for
`2 ^ -30 ≤ |x|`, `-0.293 ≤ x ≤ 0.41422`.  The exact value of `x - (x²/2 - P)` with the exact `s`
is the kernel's `2 s + s R(s)`, so the error is that of `x²/2 - P` and the kernel's.  The
difference rounds once, and `F64RoundNearest` charges no error for that rounding: negative `x` and
`x ≤ 0.285` meet the relative criterion, and `x ≥ 0.285` gives `log (1 + x) ≥ 0.2507` and an
error below one spacing of `[1/4, 1/2)`.
-/

namespace Verified.Examples.Log1pTheoremK0
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest Log1pTheoremBranches
  Log1pTheoremCore Log1pTheoremConst

set_option exponentiation.threshold 4096

/-- `x²/2 - P` through the chain, at the scale `|f|²`. -/
theorem x_approx (f : Float) (F0 Mh eh MP eP : ℝ) (hσ : |value f.toBits| ≤ F0)
    (hq : FSApprox (hfsqOf f) (value f.toBits / 2 * value f.toBits)
      (|value f.toBits| * |value f.toBits|) Mh eh)
    (hP : FSApprox (POf f) (Pstar (value f.toBits))
      (|value f.toBits| * (|value f.toBits| * |value f.toBits|)) MP eP)
    (hov : Mh + MP * F0 + (eh + eP * F0) < 2 ^ 1023) :
    FApprox (hfsqOf f - POf f) (value f.toBits / 2 * value f.toBits - Pstar (value f.toBits))
      ((eh + eP * F0 + (Mh + MP * F0 + (eh + eP * F0)) / 2 ^ 53) *
        (|value f.toBits| * |value f.toBits|)) := by
  have hk : |value f.toBits| * (|value f.toBits| * |value f.toBits|) ≤
      F0 * (|value f.toBits| * |value f.toBits|) :=
    mul_le_mul_of_nonneg_right hσ (by positivity)
  have hP' := hP.rescale (|value f.toBits| * |value f.toBits|) F0 hq.1 hq.2.1 hk
  exact (fsapprox_sub' hq hP' hov).approx

/-- The exact difference against `log (1 + v)`: the error of `X` and the kernel's. -/
theorem k0_close (f : Float) {eX : ℝ}
    (hX : FApprox (hfsqOf f - POf f)
      (value f.toBits / 2 * value f.toBits - Pstar (value f.toBits)) eX)
    (hv : -1 < value f.toBits) (hs : |sStar (value f.toBits)| ≤ 1716 / 10000) :
    0 + eX + |value f.toBits - (value f.toBits / 2 * value f.toBits - Pstar (value f.toBits)) -
      Real.log (1 + value f.toBits)| ≤
      eX + |sStar (value f.toBits)| * ((93 / 128) / 2 ^ 58) := by
  rw [tail_identity _ (by linarith), abs_sub_comm]
  have := log_kernel _ hv hs
  linarith

/-- `|s*| ≤ 0.1716` on `[-0.2929, 0.41422]`. -/
theorem sstar_le (v : ℝ) (h1 : -2929 / 10000 ≤ v) (h2 : v ≤ 41422 / 100000) :
    |sStar v| ≤ 1716 / 10000 := by
  have h3 : 0 < 2 + v := by linarith
  rw [sStar, abs_div, abs_of_pos h3, div_le_iff₀ h3]
  rcases le_or_gt 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    linarith
  · rw [abs_of_neg hv]
    linarith

theorem sstar_abs (v mb : ℝ) (hmb : 0 < mb) (h : mb ≤ 2 + v) : |sStar v| ≤ |v| / mb := by
  rw [sStar, abs_div, abs_of_pos (by linarith : 0 < 2 + v)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hmb h

theorem rel_err (e σ s y ρ F0 mb L κ : ℝ) (he : 0 ≤ e) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ F0)
    (hmb : 0 < mb) (hκ : 0 ≤ κ) (hs : |s| ≤ σ / mb) (hy : σ * L ≤ |y|) (hρ : 0 ≤ ρ)
    (hnum : e * F0 + κ / mb ≤ ρ * L) : e * (σ * σ) + |s| * κ ≤ ρ * |y| := by
  have h1 : e * (σ * σ) ≤ e * F0 * σ := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by nlinarith) he
  have h2 : |s| * κ ≤ σ / mb * κ := mul_le_mul_of_nonneg_right hs hκ
  have h3 : σ / mb * κ = κ / mb * σ := by ring
  have h4 : (e * F0 + κ / mb) * σ ≤ ρ * L * σ := mul_le_mul_of_nonneg_right hnum hσ0
  have h5 : ρ * (σ * L) ≤ ρ * |y| := mul_le_mul_of_nonneg_left hy hρ
  nlinarith

theorem abs_err (e σ s E F0 mb κ : ℝ) (he : 0 ≤ e) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ F0)
    (hmb : 0 < mb) (hκ : 0 ≤ κ) (hs : |s| ≤ σ / mb) (hnum : e * (F0 * F0) + F0 / mb * κ ≤ E) :
    e * (σ * σ) + |s| * κ ≤ E := by
  have h1 : e * (σ * σ) ≤ e * (F0 * F0) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hσ1 hσ1 hσ0 (hσ0.trans hσ1)) he
  have h2 : |s| * κ ≤ F0 / mb * κ :=
    mul_le_mul_of_nonneg_right (hs.trans (div_le_div_of_nonneg_right hσ1 hmb.le)) hκ
  linarith

theorem k0_neg (f : Float) (hf : Finite f.toBits) (hv1 : -2929 / 10000 ≤ value f.toBits)
    (hv2 : value f.toBits ≤ -1 / 2 ^ 30) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value f.toBits))
      (f - (hfsqOf f - POf f)).toBits := by
  set v := value f.toBits with hvdef
  have hσ : |v| = -v := abs_of_neg (by linarith)
  have hc := core_P1 f hf (by rw [hσ]; linarith) (by rw [hσ]; linarith) (by linarith)
  have hX := x_approx f (293 / 1000) _ _ _ _ (by rw [hσ]; linarith) hc.1 hc.2 (by norm_num)
  have hs := sstar_abs v (1707 / 1000) (by norm_num) (by linarith)
  have hs1 : |sStar v| ≤ 1716 / 10000 := sstar_le v hv1 (by linarith)
  have hcl := k0_close f hX (by linarith) hs1
  have hlog : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + v)
    linarith
  have hy : |v| ≤ |Real.log (1 + v)| := by
    rw [hσ, abs_of_neg (by linarith)]
    linarith
  have hyu : |Real.log (1 + v)| ≤ 1 := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + v)
    have h2 : (1 + v)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    rw [abs_of_neg (by linarith)]
    linarith
  have hσ0 : 0 ≤ |v| := abs_nonneg v
  have hσ1 : |v| ≤ 293 / 1000 := by rw [hσ]; linarith
  refine sub_within_rel (approx_self f.toBits hf) hX _ ((63 / 100) / 2 ^ 53) (by positivity)
    (by norm_num) (hcl.trans ?_) ?_
    (by have : (1 : ℝ) < 2 ^ 1021 := one_lt_pow₀ (by norm_num) (by norm_num); linarith)
  · exact rel_err _ |v| _ _ _ (293 / 1000) (1707 / 1000) 1 _ (by positivity) hσ0 hσ1
      (by norm_num) (by positivity) hs (by rw [mul_one]; exact hy) (by positivity) (by norm_num)
  · have : (1 : ℝ) / 2 ^ 1021 ≤ |v| := by rw [hσ]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 30)]
    linarith

theorem k0_pos_low (f : Float) (hf : Finite f.toBits) (hv1 : 1 / 2 ^ 30 ≤ value f.toBits)
    (hv2 : value f.toBits ≤ 285 / 1000) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value f.toBits))
      (f - (hfsqOf f - POf f)).toBits := by
  set v := value f.toBits with hvdef
  have hσ : |v| = v := abs_of_pos (by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 30)])
  have hc := core_P2 f hf (by rw [hσ]; linarith) (by rw [hσ]; linarith) (by linarith)
  have hX := x_approx f (285 / 1000) _ _ _ _ (by rw [hσ]; linarith) hc.1 hc.2 (by norm_num)
  have hs := sstar_abs v 2 (by norm_num) (by linarith)
  have hs1 : |sStar v| ≤ 1716 / 10000 := by
    refine hs.trans ?_
    rw [div_le_iff₀ (by norm_num), hσ]
    linarith
  have hcl := k0_close f hX (by linarith) hs1
  have hlog : v / (1 + v) ≤ Real.log (1 + v) := by
    have := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + v)
    rw [show v / (1 + v) = 1 - (1 + v)⁻¹ by field_simp; ring]
    exact this
  have hv0 : 0 < v := by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 30)]
  have hy : v / (1285 / 1000) ≤ |Real.log (1 + v)| := by
    have h1 : v / (1285 / 1000) ≤ v / (1 + v) :=
      div_le_div_of_nonneg_left hv0.le (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h2]
    linarith
  have hyu : |Real.log (1 + v)| ≤ 1 := by
    have h2 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + v)
    rw [abs_of_nonneg h2]
    linarith
  have hσ0 : 0 ≤ |v| := abs_nonneg v
  have hσ1 : |v| ≤ 285 / 1000 := by rw [hσ]; linarith
  refine sub_within_rel (approx_self f.toBits hf) hX _ ((66 / 100) / 2 ^ 53) (by positivity)
    (by norm_num) (hcl.trans ?_) ?_
    (by have : (1 : ℝ) < 2 ^ 1021 := one_lt_pow₀ (by norm_num) (by norm_num); linarith)
  · refine rel_err _ |v| _ _ _ (285 / 1000) 2 (1000 / 1285) _ (by positivity) hσ0 hσ1
      (by norm_num) (by positivity) hs ?_ (by positivity) (by norm_num)
    rw [hσ]
    calc v * (1000 / 1285) = v / (1285 / 1000) := by ring
      _ ≤ _ := hy
  · have h1 : (1 : ℝ) / 2 ^ 1021 ≤ v / (1285 / 1000) := by
      rw [le_div_iff₀ (by norm_num)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 * (1285 / 1000) ≤ 1 / 2 ^ 30)]
    linarith

theorem k0_pos_high (f : Float) (hf : Finite f.toBits) (hv1 : 285 / 1000 ≤ value f.toBits)
    (hv2 : value f.toBits ≤ 41422 / 100000) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value f.toBits))
      (f - (hfsqOf f - POf f)).toBits := by
  set v := value f.toBits with hvdef
  have hσ : |v| = v := abs_of_pos (by linarith)
  have hc := core_P3 f hf (by rw [hσ]; linarith) (by rw [hσ]; linarith) (by linarith)
  have hX := x_approx f (41422 / 100000) _ _ _ _ (by rw [hσ]; linarith) hc.1 hc.2 (by norm_num)
  have hs := sstar_abs v (2285 / 1000) (by norm_num) (by linarith)
  have hs1 : |sStar v| ≤ 1716 / 10000 := sstar_le v (by linarith) hv2
  have hcl := k0_close f hX (by linarith) hs1
  have hl0 := log_ge (285 / 1000) (2507 / 10000) 6 (by norm_num) (by norm_num) (by decide +kernel)
  have hl : (2507 / 10000 : ℝ) ≤ Real.log (1 + v) := by
    push_cast at hl0
    exact hl0.trans (Real.log_le_log (by norm_num) (by linarith))
  have hB : value (UInt64.ofNat (1021 * 2 ^ 52)) = 1 / 4 := by
    rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]
    norm_num
  refine sub_within (approx_self f.toBits hf) hX _ ((13 / 20) / 2 ^ 54) (hcl.trans ?_) 1021
    (by norm_num) (by norm_num) ?_ (by norm_num) ?_
  · exact abs_err _ |v| _ _ (41422 / 100000) (2285 / 1000) _ (by positivity) (abs_nonneg v)
      (by rw [hσ]; exact hv2) (by norm_num) (by positivity) hs (by norm_num)
  · rw [hB, abs_of_pos (by linarith)]
    have : (13 / 20 : ℝ) / 2 ^ 54 ≤ 7 / 10000 := by norm_num
    linarith
  · rw [abs_of_pos (by linarith)]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + v)
    have h2 : (1 : ℝ) ≤ 2 ^ 1022 := one_le_pow₀ (by norm_num)
    linarith

#print axioms k0_neg
#print axioms k0_pos_low
#print axioms k0_pos_high

end Verified.Examples.Log1pTheoremK0
