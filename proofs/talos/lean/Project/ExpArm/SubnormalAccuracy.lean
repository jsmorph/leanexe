import Project.ExpArm.AdjustedPath
import Project.ExpArm.SubnormalProduct
import Project.ProofKit.F64CompensatedSum
import Project.ProofKit.F64Accuracy

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

def pathCorrection (x : UInt64) : UInt64 :=
  correctionWord (reducedWord x) table[2*(reductionWord x &&& 127).toNat]!

def negativeSubnormalPath (x : UInt64) : UInt64 :=
  Wasm.IEEE64.mul 0x0010000000000000
    (F64CompensatedSum.roundedSum (negativeScale x) (Wasm.IEEE64.mul (negativeScale x) (pathCorrection x)))

theorem path_correction_bounds (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 800) :
    Finite (pathCorrection x) ∧ |value (pathCorrection x)| ≤ 1/250 := by
  let i := (reductionWord x &&& 127).toNat
  have hi : i < 128 := by
    have h : i ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  have ht := table_real_bounds i hi
  have hr := reduction_error x hf hx
  have hc := correction_rounding (reducedWord x) table[2*i]! hr.1 ht.2.1 hr.2.2 ht.2.2.2.2
  exact ⟨hc.finite, hc.magnitude.trans (by norm_num)⟩

theorem negative_scale_bounds (x : UInt64) (hf : Finite x)
    (hx : -800 ≤ value x ∧ value x ≤ -512) :
    Finite (negativeScale x) ∧
    scaleFactor (reductionInteger x/128+1022) ≤ value (negativeScale x) ∧
    (2 : ℝ)^(-300 : Int) ≤ value (negativeScale x) ∧ value (negativeScale x) ≤ (2 : ℝ)^300 := by
  have hm := negative_reduction_bounds x hf hx
  have hs := negative_scale_value (reductionWord x) (by
    change 1 ≤ 1023+(reductionInteger x/128+1022) ∧ 1023+(reductionInteger x/128+1022) < 2047
    omega)
  let i := (reductionWord x &&& 127).toNat
  let f := scaleFactor (reductionInteger x/128+1022)
  have hi : i < 128 := by
    have h : i ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  have ht := table_real_bounds i hi
  have hv : value (negativeScale x) = value (tableScaleWord i)*f := by
    dsimp [f, scaleFactor]
    rw [← mul_div_assoc]
    exact (eq_div_iff (by positivity)).mpr hs.2.2
  have hfp : 0 < f := scaleFactor_pos _
  have hlow : f ≤ value (negativeScale x) := by rw [hv]; nlinarith [ht.2.2.1]
  have hupper : value (negativeScale x) ≤ (199/100)*f := by rw [hv]; nlinarith [table_upper i hi]
  have hfl : (2 : ℝ)^(-135 : Int) ≤ f := by
    rw [show f = (2 : ℝ)^(reductionInteger x/128+1022) from scaleFactor_zpow _ (by omega)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hfu : f ≤ (2 : ℝ)^(286 : Int) := by
    rw [show f = (2 : ℝ)^(reductionInteger x/128+1022) from scaleFactor_zpow _ (by omega)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  refine ⟨hs.1, hlow, ?_, ?_⟩
  · exact (by norm_num : (2 : ℝ)^(-300 : Int) ≤ 2^(-135 : Int)).trans (hfl.trans hlow)
  · have hn : (199/100)*(2 : ℝ)^(286 : Int) ≤ (2 : ℝ)^300 := by norm_num
    linarith

theorem negative_unrounded_error (x : UInt64) (hf : Finite x)
    (hx : -800 ≤ value x ∧ value x ≤ -512) :
    |value (negativeScale x)*(1+value (pathCorrection x))-
      Real.exp (value x+1022*Real.log 2)| ≤
      (3/100000000000000000)*scaleFactor (reductionInteger x/128+1022) := by
  have hm := negative_reduction_bounds x hf hx
  have hs := negative_scale_value (reductionWord x) (by
    change 1 ≤ 1023+(reductionInteger x/128+1022) ∧ 1023+(reductionInteger x/128+1022) < 2047
    omega)
  have habs : |value x| ≤ 800 := abs_le.mpr ⟨hx.1, by linarith⟩
  have hr := reduction_error x hf habs
  have hideal := (ideal_reduction_bound x hf (habs.trans (by norm_num))).trans
    (by norm_num : (11 : ℝ)/4000 ≤ 3/1000)
  exact scaled_correction_error (value x) (reductionWord x) (reducedWord x) (negativeScale x) 1022
    (by change 0 ≤ 1023+(reductionInteger x/128+1022); omega) hs.2.2
    hr.1 hr.2.2 hideal hr.2.1

theorem negative_subnormal_accuracy (x : UInt64) (hf : Finite x)
    (hx : -800 ≤ value x ∧ value x ≤ -512)
    (hy : negativeCore x < 0x3FF0000000000000) :
    F64Accuracy.ErrorBelowOneUlp (negativeSubnormalPath x) (Real.exp (value x)) := by
  let s := negativeScale x
  let t := pathCorrection x
  let p := Wasm.IEEE64.mul s t
  have hs := negative_scale_bounds x hf hx
  have ht := path_correction_bounds x hf (abs_le.mpr ⟨hx.1, by linarith⟩)
  have hp := scale_product_bound s t hs.1 ht.1 hs.2.2.1 hs.2.2.2 ht.2
  have hsp : 0 < value s := (by positivity : (0 : ℝ) < 2^(-300 : Int)).trans_le hs.2.2.1
  have hs2 := scale_le_two_of_small_sum s p hs.1 hp.1 hsp hs.2.2.2 hp.2.1 hy
  have hr := F64CompensatedSum.scaled_sum_error s p hs.1 hp.1 ⟨hsp, hs2⟩ hp.2.1 hy
  have he := negative_unrounded_error x hf hx
  have hf2 : scaleFactor (reductionInteger x/128+1022) ≤ 2 := hs.2.1.trans hs2
  have ha : |value s*(1+value t)-Real.exp (value x+1022*Real.log 2)| ≤ 6/100000000000000000 :=
    he.trans (by nlinarith only [hf2])
  have hb : |value p-value s*value t| ≤ 2/1000000000000000000 :=
    hp.2.2.trans (div_le_div_of_nonneg_right hs2 (by norm_num))
  have hsum : |(value s+value p)-Real.exp (value x+1022*Real.log 2)| ≤
      62/1000000000000000000 := by
    rw [show (value s+value p)-Real.exp (value x+1022*Real.log 2) =
      (value p-value s*value t)+(value s*(1+value t)-Real.exp (value x+1022*Real.log 2)) by ring]
    exact (abs_add_le _ _).trans ((add_le_add hb ha).trans (by norm_num))
  have hid : Real.exp (value x+1022*Real.log 2)*(2 : ℝ)^(-1022 : Int) = Real.exp (value x) := by
    rw [Real.exp_add, show 1022*Real.log 2 = (1022 : Nat)*Real.log 2 by norm_num,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  apply F64Accuracy.of_subnormal_error _ _ hr.1 (Real.exp_pos _)
  rw [← hid]
  have hscaled : |(value s+value p)*(2 : ℝ)^(-1022 : Int)-
      Real.exp (value x+1022*Real.log 2)*(2 : ℝ)^(-1022 : Int)| ≤
      (62/1000000000000000000)*(2 : ℝ)^(-1022 : Int) := by
    rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^(-1022 : Int))]
    exact mul_le_mul_of_nonneg_right hsum (by positivity)
  have herr := (abs_sub_le (value (negativeSubnormalPath x))
    ((value s+value p)*(2 : ℝ)^(-1022 : Int))
    (Real.exp (value x+1022*Real.log 2)*(2 : ℝ)^(-1022 : Int))).trans (add_le_add hr.2 hscaled)
  exact herr.trans_lt (by norm_num)

#print axioms negative_scale_bounds
#print axioms negative_unrounded_error
#print axioms negative_subnormal_accuracy
end Project.ExpArm
