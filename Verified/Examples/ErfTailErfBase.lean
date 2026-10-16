import Verified.Examples.ErfTailCompose
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
One step for `erf x` on an interval of the tail `[1.25, 6]`, from the words of the two computed
exponentials.  `tail_erf_word` takes the exponentials' relative errors `1.405 u` as hypotheses,
which `ErfPositive.expWith_relative` supplies, and combines `ErfTailSplit.arg1_exact`,
`ErfTailEval.tail_arg2`, `ErfTailCompose.tail_compose`, and `ErfTailCompose.tail_erf`.
`erfc_lower` keeps `erfc x` above `2^-1000` up to 26, so that the product and the quotient stay
normal.
-/

namespace Verified.Examples.ErfTailErfBase
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64ErrorTrack F64Horner RealErf ErfTailBase
  ErfTailCoeffs ErfSmallBase ErfTailSplit ErfTailEval ErfTailCompose

set_option exponentiation.threshold 4096

/-- `erfc x ≥ 2^-1000` for `1 ≤ x ≤ 26`, from the asymptotic lower bound with two terms. -/
theorem erfc_lower (x : ℝ) (hx1 : 1 ≤ x) (hx : x ≤ 26) : 1 / 2 ^ 1000 ≤ erfc x := by
  have hx0 : 0 < x := by linarith
  have h := erfc_asym 2 hx0
  simp only [even_two, Even.neg_pow, one_pow, one_mul, sub_nonneg] at h
  have ha : asym 2 x = scale / 2 * Real.exp (-x ^ 2) * (x⁻¹ - 1 / 2 * x⁻¹ ^ 3) := by
    have hc0 : ((asymCoeff 0 : ℚ) : ℝ) = 1 := by norm_num [asymCoeff]
    have hc1 : ((asymCoeff 1 : ℚ) : ℝ) = -1 / 2 := by norm_num [asymCoeff]
    rw [asym, asymSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, hc0,
      hc1]
    ring
  rw [ha] at h
  have hk := scale_bounds.1
  have hs0 := scale_pos
  have hexp : 1 / (2 : ℝ) ^ 976 ≤ Real.exp (-x ^ 2) := by
    have hl := Real.log_two_gt_d9
    have hx2 : x ^ 2 ≤ 676 := by
      have h := pow_le_pow_left₀ hx0.le hx 2
      norm_num at h
      exact h
    have h1 : -(976 * Real.log 2) ≤ -x ^ 2 := by
      have : (676 : ℝ) ≤ 976 * 0.6931471803 := by norm_num
      linarith only [hx2, hl, this]
    have h2 : Real.exp (-(976 * Real.log 2)) = 1 / 2 ^ 976 := by
      rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
      norm_num
    rw [← h2]
    exact Real.exp_le_exp.mpr h1
  have hinv : x⁻¹ - 1 / 2 * x⁻¹ ^ 3 ≥ 1 / 2 * (1 / 26) := by
    have hi1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
    have hi2 : 1 / 26 ≤ x⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hx0 hx
    have ht0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    have hi3 : x⁻¹ ^ 3 ≤ x⁻¹ := by
      have h1 : x⁻¹ ^ 3 = x⁻¹ * (x⁻¹) ^ 2 := by ring
      rw [h1]
      have h2 : (x⁻¹) ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ ht0 hi1 2
        simpa using this
      exact mul_le_of_le_one_right ht0 h2
    linarith only [hi2, hi3]
  have h3 : (333038747416263463341 / 2 ^ 68 : ℝ) / 2 * (1 / 2 ^ 976) * (1 / 2 * (1 / 26)) ≤
      scale / 2 * Real.exp (-x ^ 2) * (x⁻¹ - 1 / 2 * x⁻¹ ^ 3) := by
    gcongr
  have h4 : (1 : ℝ) / 2 ^ 1000 ≤
      (333038747416263463341 / 2 ^ 68 : ℝ) / 2 * (1 / 2 ^ 976) * (1 / 2 * (1 / 26)) := by
    norm_num
  linarith

/-- `|R/S (1/x²)| ≤ 4` for `x ≥ 5/4` when `|tailF| ≤ 1`: `x erfcx x` lies between
`(2/√π)/2 (1 - 1/(2 x²))` and `(2/√π)/2`, so its logarithm lies in `[-2, 0]`. -/
theorem rs_bound (R S : List ℚ) (x : ℝ) (hx : 5 / 4 ≤ x) (hτ : |tailF R S x| ≤ 1) :
    |eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹| ≤ 4 := by
  have hx0 : 0 < x := by linarith
  have hk := scale_bounds
  have hs0 := scale_pos
  have hpos : 0 < x * erfcx x := mul_pos hx0 (erfcx_pos x)
  have hex : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  have hup : x * erfcx x ≤ 1 := by
    have h := erfc_asym 1 hx0
    simp only [pow_one, neg_mul, one_mul, neg_nonneg, sub_nonpos] at h
    have ha : asym 1 x = scale / 2 * Real.exp (-x ^ 2) * x⁻¹ := by
      have hc0 : ((asymCoeff 0 : ℚ) : ℝ) = 1 := by norm_num [asymCoeff]
      rw [asym, asymSum, Finset.sum_range_succ, Finset.sum_range_zero, hc0]
      ring
    rw [ha] at h
    have h2 : x * erfcx x = x * Real.exp (x ^ 2) * erfc x := by simp [erfcx]; ring
    have h3 : x * Real.exp (x ^ 2) * erfc x ≤ x * Real.exp (x ^ 2) * (scale / 2 * Real.exp (-x ^ 2) * x⁻¹) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h4 : x * Real.exp (x ^ 2) * (scale / 2 * Real.exp (-x ^ 2) * x⁻¹) = scale / 2 := by
      rw [show x * Real.exp (x ^ 2) * (scale / 2 * Real.exp (-x ^ 2) * x⁻¹) =
        scale / 2 * (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) * (x * x⁻¹) by ring,
        ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_inv_cancel₀ hx0.ne']
      ring
    have hk2 : (333038747416263463344 / 2 ^ 68 : ℝ) ≤ 2 := by norm_num
    have : scale / 2 ≤ 1 := by linarith [hk.2]
    linarith
  have hlo : 1 / 3 ≤ x * erfcx x := by
    have h := erfc_asym 2 hx0
    simp only [even_two, Even.neg_pow, one_pow, one_mul, sub_nonneg] at h
    have ha : asym 2 x = scale / 2 * Real.exp (-x ^ 2) * (x⁻¹ - 1 / 2 * x⁻¹ ^ 3) := by
      have hc0 : ((asymCoeff 0 : ℚ) : ℝ) = 1 := by norm_num [asymCoeff]
      have hc1 : ((asymCoeff 1 : ℚ) : ℝ) = -1 / 2 := by norm_num [asymCoeff]
      rw [asym, asymSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, hc0,
        hc1]
      ring
    rw [ha] at h
    have h2 : x * erfcx x = x * Real.exp (x ^ 2) * erfc x := by simp [erfcx]; ring
    have h3 : x * Real.exp (x ^ 2) * (scale / 2 * Real.exp (-x ^ 2) * (x⁻¹ - 1 / 2 * x⁻¹ ^ 3)) ≤
        x * Real.exp (x ^ 2) * erfc x := mul_le_mul_of_nonneg_left h (by positivity)
    have h4 : x * Real.exp (x ^ 2) * (scale / 2 * Real.exp (-x ^ 2) * (x⁻¹ - 1 / 2 * x⁻¹ ^ 3)) =
        scale / 2 * (1 - 1 / 2 * (x⁻¹) ^ 2) := by
      have he : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      rw [show x * Real.exp (x ^ 2) * (scale / 2 * Real.exp (-x ^ 2) * (x⁻¹ - 1 / 2 * x⁻¹ ^ 3)) =
        scale / 2 * (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) *
          (x * x⁻¹ - 1 / 2 * (x * x⁻¹) * x⁻¹ ^ 2) by ring, he, mul_inv_cancel₀ hx0.ne']
      ring
    have hi : (x⁻¹) ^ 2 ≤ 16 / 25 := by
      have : x⁻¹ ≤ 4 / 5 := by
        rw [inv_le_comm₀ hx0 (by norm_num)]
        linarith
      have h0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
      have := pow_le_pow_left₀ h0 this 2
      norm_num at this ⊢
      exact this
    have h5 : (1 : ℝ) / 3 ≤ scale / 2 * (1 - 1 / 2 * (x⁻¹) ^ 2) := by
      have h6 : (17 / 25 : ℝ) ≤ 1 - 1 / 2 * (x⁻¹) ^ 2 := by linarith only [hi]
      have h7 : (333038747416263463341 / 2 ^ 68 : ℝ) / 2 * (17 / 25) ≤
          scale / 2 * (1 - 1 / 2 * (x⁻¹) ^ 2) :=
        mul_le_mul (by linarith only [hk.1]) h6 (by norm_num) (by linarith only [hs0])
      have h8 : (1 : ℝ) / 3 ≤ (333038747416263463341 / 2 ^ 68 : ℝ) / 2 * (17 / 25) := by norm_num
      linarith only [h7, h8]
    linarith
  have hlog : |Real.log (x * erfcx x)| ≤ 2 := by
    rw [abs_le]
    constructor
    · rw [Real.le_log_iff_exp_le hpos]
      have h1 : Real.exp (-2) ≤ 1 / 3 := by
        have := Real.add_one_le_exp 2
        rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
        linarith
      linarith
    · have := Real.log_le_log hpos hup
      rw [Real.log_one] at this
      linarith
  have hw : eval R (x ^ 2)⁻¹ / eval S (x ^ 2)⁻¹ = tailF R S x + Real.log (x * erfcx x) + 9 / 16 := by
    simp only [tailF, tailW]
    ring
  rw [hw]
  have := abs_add_le (tailF R S x + Real.log (x * erfcx x)) (9 / 16)
  have := abs_add_le (tailF R S x) (Real.log (x * erfcx x))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 16)] at *
  linarith

/-- One step for `erf x` on `[xlo, xhi] ⊆ [1.25, 6]`, given the words of the exponentials. -/
theorem tail_erf_word (R S : List ℚ) (RW SW : List UInt64)
    (hR : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) RW R)
    (hS : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) SW S)
    (hRn : R ≠ []) (hSn : S ≠ [])
    (xlo xhi slo shi : ℚ) (hok : tailOK R S xlo xhi slo shi = true)
    (hcrit : tailEps (1405 / 1000 * uQ) (tailDelta R S xlo xhi slo shi + epsT) * (772 / 10000) <
      1 / 2 ^ 53)
    (hker : ∀ x ∈ Set.Icc (xlo : ℝ) xhi, |tailF R S x| ≤ (epsT : ℝ))
    (h54 : (5 / 4 : ℝ) ≤ xlo) (h6 : (xhi : ℝ) ≤ 6)
    (X : UInt64) (hX : Finite X) (hxl : (xlo : ℝ) ≤ value X) (hxh : value X ≤ xhi)
    (E1 E2 : UInt64)
    (hE1 : Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
        0x3FE2000000000000) →
      |value (Wasm.IEEE64.sub (Wasm.IEEE64.mul (Wasm.IEEE64.negate (zWord X)) (zWord X))
        0x3FE2000000000000)| < 512 →
      Finite E1 ∧ |value E1 - Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
        (Wasm.IEEE64.negate (zWord X)) (zWord X)) 0x3FE2000000000000))| ≤
      (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.sub (Wasm.IEEE64.mul
        (Wasm.IEEE64.negate (zWord X)) (zWord X)) 0x3FE2000000000000)))
    (hE2 : Finite (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW RW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW SW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))) →
      |value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW RW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW SW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))))| < 512 →
      Finite E2 ∧ |value E2 - Real.exp (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW RW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW SW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))| ≤
      (1405 / 1000) * unitRoundoff64 * Real.exp (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW RW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW SW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))) :
    F64SignedRounding.WithinSteps 1 (erf (value X))
      (Wasm.IEEE64.sub 0x3FF0000000000000 (Wasm.IEEE64.div (Wasm.IEEE64.mul E1 E2) X)) := by
  have hx54 : (5 / 4 : ℝ) ≤ value X := h54.trans hxl
  have hx6 : value X ≤ 6 := hxh.trans h6
  have hd := (tailOK_data R S xlo xhi slo shi hok).2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hA1f, hA1⟩ := arg1_exact X hX (by linarith) (by linarith)
  have hA2 := tail_arg2 R S RW SW hR hS hRn hSn xlo xhi slo shi hok X hX hxl hxh
  have hτ := hker (value X) ⟨hxl, hxh⟩
  obtain ⟨_, _, _, _, _, _, hz0, hzx, hgap⟩ := z_facts X hX (by linarith) (by linarith)
  have hE1' := hE1 hA1f (by
    have hz2 : value (zWord X) ^ 2 ≤ 36 := by
      have h1 : value (zWord X) ≤ 6 := by linarith
      have h2 := pow_le_pow_left₀ hz0.le h1 2
      norm_num at h2
      exact h2
    have hz3 := sq_nonneg (value (zWord X))
    rw [hA1, abs_of_neg (show -value (zWord X) ^ 2 - 9 / 16 < 0 by linarith only [hz3])]
    linarith only [hz2])
  have hτ1 : |tailF R S (value X)| ≤ 1 := by
    have : (epsT : ℝ) ≤ 1 := by norm_num [epsT]
    linarith
  have hrs := rs_bound R S (value X) hx54 hτ1
  have hE2' := hE2 hA2.1 (by
    have hd2 : ((tailDelta R S xlo xhi slo shi : ℚ) : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hd
      push_cast at h
      have : (0 : ℝ) ≤ epsT := by norm_num [epsT]
      linarith
    have hzz : |(value (zWord X) - value X) * (value (zWord X) + value X)| ≤ 72 := by
      rw [abs_mul]
      have h1 : |value (zWord X) - value X| ≤ 1 := by
        have : value X / 2 ^ 20 ≤ 1 := by
          rw [div_le_one (by norm_num)]
          linarith only [hx6, show (6 : ℝ) ≤ 2 ^ 20 by norm_num]
        rw [abs_le]; constructor <;> linarith only [this, hzx, hgap]
      have h2 : |value (zWord X) + value X| ≤ 12 := by
        rw [abs_le]; constructor <;> linarith only [hz0, hzx, hx6, hx54]
      have h3 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      linarith only [h3]
    have h3 := abs_sub_abs_le_abs_sub (value (Wasm.IEEE64.add
        (Wasm.IEEE64.mul (Wasm.IEEE64.sub (zWord X) X) (Wasm.IEEE64.add (zWord X) X))
        (Wasm.IEEE64.div (hornerW RW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X)))
          (hornerW SW (Wasm.IEEE64.div 0x3FF0000000000000 (Wasm.IEEE64.mul X X))))))
      ((value (zWord X) - value X) * (value (zWord X) + value X) +
        eval R (value X ^ 2)⁻¹ / eval S (value X ^ 2)⁻¹)
    have h4 := abs_add_le ((value (zWord X) - value X) * (value (zWord X) + value X))
      (eval R (value X ^ 2)⁻¹ / eval S (value X ^ 2)⁻¹)
    have h5 := hA2.2
    linarith)
  have hk : ((1405 / 1000 * uQ : ℚ) : ℝ) = (1405 / 1000) * unitRoundoff64 := by
    rw [← uQ_eq]
    push_cast
    ring
  have hdelta0 : (0 : ℚ) ≤ tailDelta R S xlo xhi slo shi := by
    have h := (abs_nonneg _).trans hA2.2
    exact_mod_cast h
  have hc := tail_compose R S (1405 / 1000 * uQ) (tailDelta R S xlo xhi slo shi + epsT)
    (by norm_num [uQ]) (by
      have : (0 : ℚ) ≤ epsT := by norm_num [epsT]
      linarith) hd (by norm_num [uQ]) X (zWord X) _ _ E1 E2 hX (by linarith) (by linarith)
    (erfc_lower _ (by linarith) (by linarith)) hA1 (by rw [hk]; exact hE1') (by rw [hk]; exact hE2')
    (by
      push_cast
      have := hA2.2
      linarith)
  exact tail_erf _ hcrit X _ hX hx54 hc.1 hc.2

#print axioms erfc_lower
#print axioms rs_bound
#print axioms tail_erf_word

end Verified.Examples.ErfTailErfBase
