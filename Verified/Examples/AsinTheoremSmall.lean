import Verified.Examples.AsinTheoremRatio
import Verified.Examples.AsinTheoremBranches
import LeanExe.ProofKit.F64RoundNearest
import LeanExe.ProofKit.F64WithinSelf

/-!
`Asin.asin x` for `|x| < 1/2`.  Below `2 ^ -26` the result is `x`, which lies within
`|x| ^ 3 / 5` of `arcsin x`.  Above, the result is `x + x r(x x)`, whose exact value differs from
`arcsin x` by the kernel's error `(11/16) 2 ^ -56 |x| ^ 3` and the error of the product `x r`,
both relative to `|x| ≤ |arcsin x|`; the last sum rounds once, which the criterion of
`F64RoundNearest` does not charge.
-/

namespace Verified.Examples.AsinTheoremSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest PolyBound AsinTheoremSupport
  AsinTheoremRatio AsinTheoremBranches

set_option exponentiation.threshold 4096

/-- `|arcsin x| ≥ |x|`. -/
theorem abs_le_abs_arcsin (x : ℝ) (h : |x| ≤ 1) : |x| ≤ |Real.arcsin x| := by
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y ≤ Real.arcsin y := by
    intro y h0 h1
    have ha : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr h0
    have hs := Real.sin_le ha
    rw [Real.sin_arcsin (by linarith) h1] at hs
    exact hs
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (Real.arcsin_nonneg.mpr hx)]
    exact key x hx (by rw [abs_of_nonneg hx] at h; exact h)
  · rw [abs_of_neg hx, abs_of_nonpos (Real.arcsin_nonpos.mpr hx.le)]
    have := key (-x) (by linarith) (by rw [abs_of_neg hx] at h; exact h)
    rw [Real.arcsin_neg] at this
    linarith

/-- The kernel in the chain's form: `arcsin z` against `z + z (z ^ 2 P/Q)`. -/
theorem asin_kernel (z : ℝ) (hz : |z| ≤ 1 / 2) :
    |Real.arcsin z - (z + z * (z * z * eval AsinKernelPoly.asinP (z * z) /
      eval AsinKernelPoly.asinQ (z * z)))| ≤ |z| ^ 3 * ((11 / 16) / 2 ^ 56) := by
  have h := AsinKernelPoly.asin_kernel_error z hz
  rw [show z * z = z ^ 2 by ring]
  have heq : z + z * (z ^ 2 * eval AsinKernelPoly.asinP (z ^ 2) /
      eval AsinKernelPoly.asinQ (z ^ 2)) =
      z + z ^ 3 * (eval AsinKernelPoly.asinP (z ^ 2) / eval AsinKernelPoly.asinQ (z ^ 2)) := by
    ring
  rw [heq, show Real.arcsin z - (z + z ^ 3 * (eval AsinKernelPoly.asinP (z ^ 2) /
    eval AsinKernelPoly.asinQ (z ^ 2))) = Real.arcsin z - z - z ^ 3 *
      (eval AsinKernelPoly.asinP (z ^ 2) / eval AsinKernelPoly.asinQ (z ^ 2)) by ring]
  exact h

/-- The chain's value of `asinRatio` as the kernel's quotient. -/
theorem ratio_eval (vt : ℝ) :
    vt * (value 0x3FC5555555555555 + vt * (value 0xBFD4D61203EB6F7D + vt *
      (value 0x3FC9C1550E884455 + vt * (value 0xBFA48228B5688F3B + vt *
        (value 0x3F49EFE07501B288 + vt * value 0x3F023DE10DFDF709))))) /
      (1 + vt * (value 0xC0033A271C8A2D4B + vt * (value 0x40002AE59C598AC8 + vt *
        (value 0xBFE6066C1B8D0159 + vt * value 0x3FB3B8C5B12E9282)))) =
    vt * eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt := by
  simp only [AsinKernelPoly.asinP, AsinKernelPoly.asinQ, eval_cons, eval_nil, mul_zero, add_zero,
    ratOfWord_cast]
  push_cast
  ring

theorem abs_arcsin_lt (v : ℝ) : |Real.arcsin v| < 2 := by
  have h1 := Real.arcsin_le_pi_div_two v
  have h2 := Real.neg_pi_div_two_le_arcsin v
  have h3 := Real.pi_lt_four
  rw [abs_lt]
  constructor <;> linarith

/-- `x + x r(x x)` from a chain for `r` at the scale `x ^ 2`. -/
theorem small_finish (x : Float) (hx : Finite x.toBits) (T0 Mr er ρ : ℝ)
    (hr : FSApprox (Asin.asinRatio (x * x))
      (value x.toBits * value x.toBits * eval AsinKernelPoly.asinP (value x.toBits * value x.toBits) /
        eval AsinKernelPoly.asinQ (value x.toBits * value x.toBits))
      (|value x.toBits| * |value x.toBits|) Mr er) (hMr2 : Mr ≤ 1) (her2 : er ≤ 1)
    (hσ2 : |value x.toBits| * |value x.toBits| ≤ T0) (hσ0 : 1 / 2 ^ 26 ≤ |value x.toBits|)
    (hσ1 : |value x.toBits| < 1 / 2)
    (hρn : T0 * (0 * Mr + 1 * er + 0 * er + (1 + 0) * (Mr + er) / 2 ^ 53 + 1 / 2 ^ 960 +
      (11 / 16) / 2 ^ 56) ≤ ρ) (hρ : ρ ≤ 1 / (2 ^ 53 + 1)) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits))
      (x + x * Asin.asinRatio (x * x)).toBits := by
  set v := value x.toBits with hv
  set σ := |v| with hσ
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hfx : FSApprox x v σ 1 0 := fsapprox_input x hx σ hσp (by linarith) le_rfl
  have hss : 1 / 2 ^ 52 ≤ σ * σ := by
    have := mul_le_mul hσ0 hσ0 (by positivity) hσp.le
    norm_num at this ⊢
    linarith
  have hη3 : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) := by
    have h3 : 1 / 2 ^ 26 * (1 / 2 ^ 52) ≤ σ * (σ * σ) := mul_le_mul hσ0 hss (by positivity) hσp.le
    have : 1 / 2 ^ 960 * (1 / 2 ^ 26 * (1 / 2 ^ 52)) ≤ 1 / 2 ^ 960 * (σ * (σ * σ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    norm_num at this ⊢
    linarith
  have hMr := hr.M_nonneg
  have her := hr.e_nonneg
  have hxr := fsapprox_mul hfx hr (1 / 2 ^ 960) hη3 (by nlinarith)
  have hker := asin_kernel v (by linarith)
  have hy := abs_le_abs_arcsin v (by linarith)
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρn
  refine add_within_rel (approx_self x.toBits hx) hxr.approx (Real.arcsin v) ρ hρ0 hρ ?_ ?_
    (lt_trans (abs_arcsin_lt v) (by norm_num))
  · rw [abs_sub_comm] at hker
    have hc : |v + v * (v * v * eval AsinKernelPoly.asinP (v * v) /
        eval AsinKernelPoly.asinQ (v * v)) - Real.arcsin v| ≤ σ * (σ * σ) * ((11 / 16) / 2 ^ 56) := by
      refine hker.trans (le_of_eq ?_)
      rw [hσ]
      ring
    set e := 0 * Mr + 1 * er + 0 * er + (1 + 0) * (Mr + er) / 2 ^ 53 + 1 / 2 ^ 960 with he
    have he0 : 0 ≤ e := by rw [he]; positivity
    have h3 : σ * (σ * σ) ≤ σ * T0 := by
      rw [← mul_assoc, mul_comm σ σ, mul_assoc]
      nlinarith
    have h4 : (e + (11 / 16) / 2 ^ 56) * (σ * (σ * σ)) ≤ (e + (11 / 16) / 2 ^ 56) * (σ * T0) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : ρ * σ ≤ ρ * |Real.arcsin v| := mul_le_mul_of_nonneg_left hy hρ0
    nlinarith
  · have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 26 := by norm_num
    linarith

/-- `x` for `|x| < 2 ^ -26`. -/
theorem tiny_within (x : Float) (hx : Finite x.toBits) (h : |value x.toBits| < 1 / 2 ^ 26) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits)) x.toBits := by
  set v := value x.toBits with hv
  refine F64WithinSelf.within_one_of_self x.toBits hx _ (1 / 2 ^ 53) (by positivity) le_rfl ?_
  have hker := asin_kernel v (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 26 ≤ 1 / 2)])
  -- `|P/Q| ≤ 1/5` near zero
  have hP := poly_bound AsinKernelPoly.asinP 0 (1 / 2 ^ 52) (1 / 5) 4 (by decide +kernel) (v * v)
    (by push_cast; positivity) (by
      push_cast
      have := mul_le_mul h.le h.le (abs_nonneg v) (by positivity)
      rw [abs_mul_abs_self] at this
      norm_num at this ⊢
      linarith)
  have hQ := poly_bound (subP AsinKernelPoly.asinQ [1]) 0 (1 / 2 ^ 52) (1 / 100) 4
    (by decide +kernel) (v * v) (by push_cast; positivity) (by
      push_cast
      have := mul_le_mul h.le h.le (abs_nonneg v) (by positivity)
      rw [abs_mul_abs_self] at this
      norm_num at this ⊢
      linarith)
  rw [eval_subP] at hQ
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hQ
  push_cast at hP hQ
  have hQl : 99 / 100 ≤ eval AsinKernelPoly.asinQ (v * v) := by
    have := (abs_le.mp hQ).1
    linarith
  have hvv : v * v ≤ 1 / 2 ^ 52 := by
    have := mul_le_mul h.le h.le (abs_nonneg v) (by positivity)
    rw [abs_mul_abs_self] at this
    norm_num at this ⊢
    linarith
  have hq : |v * (v * v * eval AsinKernelPoly.asinP (v * v) / eval AsinKernelPoly.asinQ (v * v))| ≤
      |v| * (1 / 2 ^ 52 * (1 / 5) / (99 / 100)) := by
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (mul_self_nonneg v),
      abs_of_pos (by linarith : (0 : ℝ) < eval AsinKernelPoly.asinQ (v * v))]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg v)
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have := mul_le_mul hvv hP (abs_nonneg _) (by positivity)
    nlinarith
  have hv3 : |v| ^ 3 * ((11 / 16) / 2 ^ 56) ≤ |v| * (1 / 2 ^ 52 * ((11 / 16) / 2 ^ 56)) := by
    have : |v| ^ 2 ≤ 1 / 2 ^ 52 := by
      rw [sq_abs, sq]
      exact hvv
    nlinarith [abs_nonneg v]
  have htri := abs_sub (Real.arcsin v - (v + v * (v * v * eval AsinKernelPoly.asinP (v * v) /
    eval AsinKernelPoly.asinQ (v * v)))) (-(v * (v * v * eval AsinKernelPoly.asinP (v * v) /
      eval AsinKernelPoly.asinQ (v * v))))
  rw [abs_neg] at htri
  rw [abs_sub_comm, show Real.arcsin v - v = Real.arcsin v - (v + v * (v * v *
    eval AsinKernelPoly.asinP (v * v) / eval AsinKernelPoly.asinQ (v * v))) -
      -(v * (v * v * eval AsinKernelPoly.asinP (v * v) / eval AsinKernelPoly.asinQ (v * v))) by
        ring]
  have hn : |v| * (1 / 2 ^ 52 * (1 / 5) / (99 / 100)) + |v| * (1 / 2 ^ 52 * ((11 / 16) / 2 ^ 56)) ≤
      1 / 2 ^ 53 * |v| := by
    have h0 := abs_nonneg v
    have : (1 : ℝ) / 2 ^ 52 * (1 / 5) / (99 / 100) + 1 / 2 ^ 52 * ((11 / 16) / 2 ^ 56) ≤
        1 / 2 ^ 53 := by norm_num
    nlinarith
  linarith

end Verified.Examples.AsinTheoremSmall
