import Verified.Examples.AtanTheoremCases
import LeanExe.ProofKit.F64WithinSelf

/-!
`Atan.atan` below `0.4375` in magnitude.  Below `2 ^ -27` the result is `x`, which lies within
`|x| ^ 3` of `arctan x`.  From `2 ^ -27` to `1/4` the error of `x - x * atanS x` is relative to `|x|`
and `F64WithinSelf.rel_finish` uses the binade of `x`.  From `1/4` to `0.4375` the error is absolute,
in the binade `[1/8, 1/4)` up to `0.2556` and `[1/4, 1/2)` beyond.
-/

namespace Verified.Examples.AtanTheoremSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound AtanTheoremPoly AtanTheoremBranches
  AtanTheoremTail AtanTheoremConst AtanTheoremReduce AtanTheoremCases F64WithinSelf

set_option exponentiation.threshold 4096

theorem arctan_near (v : ℝ) (hv : |v| < 1) : |Real.arctan v - v| ≤ |v| ^ 3 / (1 - v ^ 2) := by
  have hr := TaylorRemainder.atan_remainder v hv 1
  have he : v * eval (TaylorRemainder.atanCoeffs 1) (v ^ 2) = v := by
    simp [TaylorRemainder.atanCoeffs, eval_cons]
  rw [he] at hr
  simpa using hr

theorem arctan_ge_quintic (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) :
    v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / (1 - v ^ 2) ≤ Real.arctan v := by
  have hr := TaylorRemainder.atan_remainder v (by rw [abs_of_nonneg h0]; linarith) 3
  have he : v * eval (TaylorRemainder.atanCoeffs 3) (v ^ 2) = v - v ^ 3 / 3 + v ^ 5 / 5 := by
    simp [TaylorRemainder.atanCoeffs, eval_cons, List.range_succ]
    ring
  rw [he, abs_of_nonneg h0] at hr
  have := (abs_le.mp hr).1
  linarith

theorem abs_arctan (v : ℝ) : |Real.arctan v| = Real.arctan |v| := by
  rcases le_total 0 v with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg]
    have := Real.arctan_mono h
    rwa [Real.arctan_zero] at this
  · rw [abs_of_nonpos h, abs_of_nonpos, Real.arctan_neg]
    have := Real.arctan_mono h
    rwa [Real.arctan_zero] at this

theorem atan_tiny (x : Float) (hx : Finite x.toBits) (hs : |value x.toBits| < 1 / 2 ^ 27) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) x.toBits := by
  set v := value x.toBits with hv
  have hv1 : |v| < 1 := hs.trans (by norm_num)
  have hn := arctan_near v hv1
  have hv2 : v ^ 2 ≤ 1 / 2 ^ 54 := by
    rw [← sq_abs]
    have := mul_le_mul hs.le hs.le (abs_nonneg v) (by positivity)
    nlinarith
  apply within_one_of_self x.toBits hx _ (1 / 2 ^ 53) (by positivity) le_rfl
  rw [abs_sub_comm]
  refine hn.trans ?_
  rw [div_le_iff₀ (by nlinarith)]
  have h3 : |v| ^ 3 = |v| * v ^ 2 := by rw [pow_succ', sq_abs]
  rw [h3]
  have hv0 := abs_nonneg v
  have : |v| * v ^ 2 ≤ |v| * (1 / 2 ^ 54) := mul_le_mul_of_nonneg_left hv2 hv0
  nlinarith

theorem atan_poly_small_err (x : Float) (hx : Finite x.toBits)
    (h1 : 1 / 2 ^ 27 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ 1 / 4) :
    Finite (x - x * atanS x).toBits ∧
      |value (x - x * atanS x).toBits - Real.arctan (value x.toBits)| ≤
        12 / 10 / 2 ^ 53 * |value x.toBits| := by
  set v := value x.toBits with hv
  set s := |v| with hsdef
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) h1
  have hxs : FSApprox x v s 1 0 := fsapprox_input x hx s hs0 (by linarith) le_rfl
  have hP := atanS_approx x s hxs (by linarith) h1
  have hPM : |v * polyS v| ≤ 3779 / 10000 * (s * (s * s)) := hP.2.2.1
  have hs3 : s * (s * s) ≤ 1 / 16 * s := by nlinarith
  have hMr : |v - v * polyS v| ≤ 10237 / 10000 * s := by
    calc |v - v * polyS v| ≤ |v| + |v * polyS v| := abs_sub _ _
      _ ≤ s + 3779 / 10000 * (1 / 16 * s) := by
          gcongr
          exact hPM.trans (mul_le_mul_of_nonneg_left hs3 (by norm_num))
      _ ≤ 10237 / 10000 * s := by nlinarith
  obtain ⟨hcf, hc⟩ := poly_result x s (1 / 4) (10237 / 10000) hxs h2 (by norm_num) h1 hMr
    (by norm_num)
  have hk := AtanKernelPoly.atan_kernel_error v (by linarith)
  rw [← kernel_link, ← hsdef] at hk
  have htot : |value (x - x * atanS x).toBits - Real.arctan v| ≤
      (polyErr (1 / 4) (10237 / 10000) + 5 / 8 / 2 ^ 57) * s := by
    have := abs_sub_le (value (x - x * atanS x).toBits) (v - v * polyS v) (Real.arctan v)
    rw [abs_sub_comm (v - v * polyS v)] at this
    linarith
  have hρ : polyErr (1 / 4) (10237 / 10000) + 5 / 8 / 2 ^ 57 ≤ 12 / 10 / 2 ^ 53 := by
    norm_num [polyErr]
  exact ⟨hcf, htot.trans (mul_le_mul_of_nonneg_right hρ hs0.le)⟩

theorem atan_poly_small (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ^ 27 ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ 1 / 4) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) (x - x * atanS x).toBits := by
  set v := value x.toBits with hv
  set s := |v| with hsdef
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) h1
  obtain ⟨hcf, htot⟩ := atan_poly_small_err x hx h1 h2
  have hexp : 2 ≤ Wasm.IEEE64.exponent x.toBits := by
    by_contra hn
    have h := F64Magnitude.magnitude_lt x.toBits 2 (-1021) (by norm_num) (by norm_num) (by omega)
    have h2' : (2 : ℝ) ^ (-1021 : ℤ) < 1 / 2 ^ 27 := by norm_num
    have h3 : s < 1 / 2 ^ 27 := by
      rw [hsdef, hv]
      exact h.trans h2'
    linarith
  have hb := binade_bounds x.toBits hx (by omega)
  have hlow : (1 - 1 / 15) * s ≤ |Real.arctan v| := by
    rw [abs_arctan]
    have hn := arctan_near s (by rw [abs_of_pos hs0]; linarith)
    rw [abs_of_pos hs0] at hn
    have h3 : s ^ 3 / (1 - s ^ 2) ≤ s / 15 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have := (abs_le.mp hn).1
    linarith
  exact rel_finish _ hcf (Real.arctan v) s (Wasm.IEEE64.exponent x.toBits) hexp
    (by have := F64UpperWord.finite_high x.toBits hx; rw [F64UpperWord.high_toNat] at this;
        simp only [Wasm.IEEE64.exponent]; omega)
    hb.1 hb.2 (1 / 15) (12 / 10 / 2 ^ 53) (by norm_num) (by positivity)
    htot hlow (by norm_num) (by norm_num)

theorem atan_poly_mid_a_err (x : Float) (hx : Finite x.toBits) (h1 : 1 / 4 ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ 2556 / 10000) :
    Finite (x - x * atanS x).toBits ∧
      |value (x - x * atanS x).toBits - Real.arctan (value x.toBits)| ≤ 1222 / 1000 / 2 ^ 55 ∧
      value (UInt64.ofNat (1020 * 2 ^ 52)) + 1222 / 1000 / 2 ^ 55 + 1 / 2 ^ 52 ≤
        |Real.arctan (value x.toBits)| := by
  set v := value x.toBits with hv
  have hxs : FSApprox x v (2556 / 10000) 1 0 :=
    fsapprox_input x hx _ (by norm_num) (by norm_num) h2
  have hP := atanS_approx x _ hxs (by norm_num) (by norm_num)
  have hPM : |v * polyS v| ≤ 3779 / 10000 * (2556 / 10000 * (2556 / 10000 * (2556 / 10000))) :=
    hP.2.2.1
  have hMr : |v - v * polyS v| ≤ 10247 / 10000 * (2556 / 10000) := by
    calc |v - v * polyS v| ≤ |v| + |v * polyS v| := abs_sub _ _
      _ ≤ 10247 / 10000 * (2556 / 10000) := by norm_num at hPM ⊢; linarith
  obtain ⟨hcf, hc⟩ := poly_result x (2556 / 10000) (2556 / 10000) (10247 / 10000) hxs le_rfl
    (by norm_num) (by norm_num) hMr (by norm_num)
  have hk := AtanKernelPoly.atan_kernel_error v (by linarith)
  rw [← kernel_link] at hk
  have hk' : |v| * (5 / 8 / 2 ^ 57) ≤ 2556 / 10000 * (5 / 8 / 2 ^ 57) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have htot : |value (x - x * atanS x).toBits - Real.arctan v| ≤
      polyErr (2556 / 10000) (10247 / 10000) * (2556 / 10000) + 2556 / 10000 * (5 / 8 / 2 ^ 57) := by
    have := abs_sub_le (value (x - x * atanS x).toBits) (v - v * polyS v) (Real.arctan v)
    rw [abs_sub_comm (v - v * polyS v)] at this
    linarith
  have hlow : 1 / 4 - (1 / 4) ^ 3 / (1 - (1 / 4) ^ 2) ≤ |Real.arctan v| := by
    rw [abs_arctan]
    have hn := arctan_near (1 / 4) (by norm_num)
    have hm := Real.arctan_mono h1
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hn
    have := (abs_le.mp hn).1
    linarith
  refine ⟨hcf, htot.trans (by norm_num [polyErr]), ?_⟩
  rw [F64PositiveSpacing.boundary_value 1020 (by norm_num) (by norm_num)]
  norm_num at hlow ⊢
  linarith

theorem atan_poly_mid_a (x : Float) (hx : Finite x.toBits) (h1 : 1 / 4 ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ 2556 / 10000) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) (x - x * atanS x).toBits := by
  obtain ⟨hcf, htot, hlow⟩ := atan_poly_mid_a_err x hx h1 h2
  refine abs_finish _ hcf _ _ 1020 (by norm_num) (by norm_num) htot ?_ (by norm_num)
  generalize value (UInt64.ofNat (1020 * 2 ^ 52)) = B at hlow ⊢
  linarith

theorem atan_poly_mid_b_err (x : Float) (hx : Finite x.toBits)
    (h1 : 2556 / 10000 ≤ |value x.toBits|) (h2 : |value x.toBits| ≤ 7 / 16) :
    Finite (x - x * atanS x).toBits ∧
      |value (x - x * atanS x).toBits - Real.arctan (value x.toBits)| ≤ 1308 / 1000 / 2 ^ 54 ∧
      value (UInt64.ofNat (1021 * 2 ^ 52)) + 1308 / 1000 / 2 ^ 54 + 1 / 2 ^ 52 ≤
        |Real.arctan (value x.toBits)| := by
  set v := value x.toBits with hv
  have hxs : FSApprox x v (7 / 16) 1 0 := fsapprox_input x hx _ (by norm_num) (by norm_num) h2
  have hP := atanS_approx x _ hxs (by norm_num) (by norm_num)
  have hPM : |v * polyS v| ≤ 3779 / 10000 * (7 / 16 * (7 / 16 * (7 / 16))) := hP.2.2.1
  have hMr : |v - v * polyS v| ≤ 10724 / 10000 * (7 / 16) := by
    calc |v - v * polyS v| ≤ |v| + |v * polyS v| := abs_sub _ _
      _ ≤ 10724 / 10000 * (7 / 16) := by norm_num at hPM ⊢; linarith
  obtain ⟨hcf, hc⟩ := poly_result x (7 / 16) (7 / 16) (10724 / 10000) hxs le_rfl
    (by norm_num) (by norm_num) hMr (by norm_num)
  have hk := AtanKernelPoly.atan_kernel_error v h2
  rw [← kernel_link] at hk
  have hk' : |v| * (5 / 8 / 2 ^ 57) ≤ 7 / 16 * (5 / 8 / 2 ^ 57) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have htot : |value (x - x * atanS x).toBits - Real.arctan v| ≤
      polyErr (7 / 16) (10724 / 10000) * (7 / 16) + 7 / 16 * (5 / 8 / 2 ^ 57) := by
    have := abs_sub_le (value (x - x * atanS x).toBits) (v - v * polyS v) (Real.arctan v)
    rw [abs_sub_comm (v - v * polyS v)] at this
    linarith
  have hlow : 2556 / 10000 - (2556 / 10000) ^ 3 / 3 + (2556 / 10000) ^ 5 / 5 -
      (2556 / 10000) ^ 7 / (1 - (2556 / 10000) ^ 2) ≤ |Real.arctan v| := by
    rw [abs_arctan]
    exact (arctan_ge_quintic _ (by norm_num) (by norm_num)).trans (Real.arctan_mono h1)
  refine ⟨hcf, htot.trans (by norm_num [polyErr]), ?_⟩
  rw [F64PositiveSpacing.boundary_value 1021 (by norm_num) (by norm_num)]
  norm_num at hlow ⊢
  linarith

theorem atan_poly_mid_b (x : Float) (hx : Finite x.toBits) (h1 : 2556 / 10000 ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ 7 / 16) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) (x - x * atanS x).toBits := by
  obtain ⟨hcf, htot, hlow⟩ := atan_poly_mid_b_err x hx h1 h2
  refine abs_finish _ hcf _ _ 1021 (by norm_num) (by norm_num) htot ?_ (by norm_num)
  generalize value (UInt64.ofNat (1021 * 2 ^ 52)) = B at hlow ⊢
  linarith

#print axioms atan_tiny
#print axioms atan_poly_small
#print axioms atan_poly_mid_a
#print axioms atan_poly_mid_b

end Verified.Examples.AtanTheoremSmall
