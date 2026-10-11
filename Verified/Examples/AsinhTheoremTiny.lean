import Verified.Examples.AsinhTheoremBranches
import Verified.Examples.Log1pTheoremTail
import LeanExe.ProofKit.F64WithinSelf
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
`Asinh.asinh x` and `Asinh.atanh x` for `|x| < 2 ^ -28`, where both return `x`.  `arsinh x` and
`artanh x` lie within `|x| ³` of `x`: the first by the mean value theorem, since the derivative of
`arsinh t - t` is at most `t²` in magnitude, and the second from the cubic bounds of `log (1 ± x)`.
The result is then within one step by `F64WithinSelf.within_one_of_self`.  The file also states the
branches of `Asinh.atanh`.
-/

namespace Verified.Examples.AsinhTheoremTiny
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches AsinhTheoremBranches

set_option exponentiation.threshold 4096

theorem arsinh_tiny (v : ℝ) (hv : |v| ≤ 1) : |Real.arsinh v - v| ≤ |v| ^ 3 := by
  set r := |v| with hr
  have hd : ∀ t ∈ Set.Icc (-r) r,
      HasDerivWithinAt (fun s => Real.arsinh s - s) ((Real.sqrt (1 + t ^ 2))⁻¹ - 1)
        (Set.Icc (-r) r) t :=
    fun t _ => ((Real.hasDerivAt_arsinh t).sub (hasDerivAt_id t)).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (-r) r, ‖(Real.sqrt (1 + t ^ 2))⁻¹ - 1‖ ≤ r ^ 2 := by
    intro t ht
    have ht2 : t ^ 2 ≤ r ^ 2 := by
      have h := abs_le.mpr ⟨ht.1, ht.2⟩
      rw [← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg t) h 2
    have hr0 : 0 ≤ r := abs_nonneg v
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    have hs1 : 1 ≤ Real.sqrt (1 + t ^ 2) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [sq_nonneg t]
    have hs2 : Real.sqrt (1 + t ^ 2) ≤ 1 + t ^ 2 / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg (t ^ 2)]
    have hsp : 0 < Real.sqrt (1 + t ^ 2) := by linarith
    have h12 : 0 ≤ 1 - t ^ 2 / 2 := by linarith
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h3 : 1 - t ^ 2 / 2 ≤ (Real.sqrt (1 + t ^ 2))⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hsp]
        nlinarith [mul_le_mul_of_nonneg_left hs2 h12, sq_nonneg (t ^ 2)]
      linarith
    · have h3 : (Real.sqrt (1 + t ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
      nlinarith [sq_nonneg t]
  have hmem0 : (0 : ℝ) ∈ Set.Icc (-r) r := ⟨by linarith [abs_nonneg v], abs_nonneg v⟩
  have hmemv : v ∈ Set.Icc (-r) r := ⟨neg_abs_le v, le_abs_self v⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc (-r) r)
    hmem0 hmemv
  simp only [Real.arsinh_zero, sub_zero, Real.norm_eq_abs] at h
  rw [show r ^ 3 = r ^ 2 * r by ring]
  exact h

theorem artanh_tiny (v : ℝ) (hv : |v| ≤ 1 / 2) : |Real.artanh v - v| ≤ 2 * |v| ^ 3 := by
  have h1 := Log1pTheoremTail.log_cubic v hv
  have h2 := Log1pTheoremTail.log_cubic (-v) (by rw [abs_neg]; exact hv)
  have hv' := abs_le.mp hv
  rw [show (-v) ^ 2 = v ^ 2 by ring, show (-v) ^ 3 = -v ^ 3 by ring,
    show (-v) ^ 4 = v ^ 4 by ring] at h2
  have heq : Real.artanh v = (Real.log (1 + v) - Real.log (1 + -v)) / 2 := by
    rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩, Real.log_div (by linarith)
      (by linarith), ← sub_eq_add_neg]
    ring
  rw [heq]
  have e4 : v ^ 4 = |v| ^ 3 * |v| := by
    rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, ← sq_abs v]
    ring
  have h4 : v ^ 4 ≤ |v| ^ 3 / 2 := by
    have := mul_le_mul_of_nonneg_left hv (pow_nonneg (abs_nonneg v) 3)
    rw [e4]
    linarith
  have hc := abs_le.mp (le_of_eq (abs_pow v 3))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hc.1, hc.2]

/-- `|x| < 2 ^ -28`: `asinh x = x`. -/
theorem asinh_tiny (x : Float) (hx : Finite x.toBits) (hs : |value x.toBits| < 1 / 2 ^ 28) :
    F64SignedRounding.WithinSteps 1 (Real.arsinh (value x.toBits)) x.toBits := by
  have h3 := arsinh_tiny (value x.toBits) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 28 ≤ 1)])
  refine F64WithinSelf.within_one_of_self x.toBits hx _ (1 / 2 ^ 56) (by positivity)
    (by norm_num) ?_
  rw [abs_sub_comm]
  refine h3.trans ?_
  have h4 : |value x.toBits| ^ 2 ≤ 1 / 2 ^ 56 := by
    have := mul_le_mul hs.le hs.le (abs_nonneg _) (by positivity)
    nlinarith
  calc |value x.toBits| ^ 3 = |value x.toBits| ^ 2 * |value x.toBits| := by ring
    _ ≤ 1 / 2 ^ 56 * |value x.toBits| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)

/-- `|x| < 2 ^ -28`: `atanh x = x`. -/
theorem atanh_tiny_within (x : Float) (hx : Finite x.toBits)
    (hs : |value x.toBits| < 1 / 2 ^ 28) :
    F64SignedRounding.WithinSteps 1 (Real.artanh (value x.toBits)) x.toBits := by
  have h3 := artanh_tiny (value x.toBits) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 28 ≤ 1 / 2)])
  refine F64WithinSelf.within_one_of_self x.toBits hx _ (1 / 2 ^ 55) (by positivity)
    (by norm_num) ?_
  rw [abs_sub_comm]
  refine h3.trans ?_
  have h4 : |value x.toBits| ^ 2 ≤ 1 / 2 ^ 56 := by
    have := mul_le_mul hs.le hs.le (abs_nonneg _) (by positivity)
    nlinarith
  calc 2 * |value x.toBits| ^ 3 = 2 * |value x.toBits| ^ 2 * |value x.toBits| := by ring
    _ ≤ 2 * (1 / 2 ^ 56) * |value x.toBits| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith
    _ = 1 / 2 ^ 55 * |value x.toBits| := by ring

#print axioms asinh_tiny
#print axioms atanh_tiny_within

end Verified.Examples.AsinhTheoremTiny
