import Project.LayerNorm.Model
import Project.LayerNorm.Real
import Project.ProofKit.F64ArithmeticBounds

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem four_value : value 0x4010000000000000 = 4 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem sum_four (f : Fin 4 → ℝ) : (∑ i, f i) = (f 0 + f 1) + (f 2 + f 3) := by
  simp [Fin.sum_univ_succ]
  ring

theorem mean_magnitude (x : Real.Row) (bound : ℝ) (h : ∀ i, |x i| ≤ bound) :
    |Real.mean x| ≤ bound := by
  rw [Real.mean, abs_div]
  norm_num
  have hs : |∑ i, x i| ≤ 4 * bound :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp))
  linarith only [hs]

theorem average_error (x : Fin 4 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hbmax : bound ≤ 256)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound) :
    Finite (average (x 0) (x 1) (x 2) (x 3)) ∧
    |value (average (x 0) (x 1) (x 2) (x 3))| ≤ 2 * bound ∧
    |value (average (x 0) (x 1) (x 2) (x 3)) - Real.mean (fun i => value (x i))| ≤
      5 * bound * arithmeticEpsilon := by
  have hu : 0 < arithmeticEpsilon := F64ArithmeticBounds.epsilon_pos
  have he : arithmeticEpsilon ≤ 1/10 := by norm_num [arithmeticEpsilon]
  have pair (i j : Fin 4) := F64ArithmeticBounds.add_error (x i) (x j) (hf i) (hf j)
    (2*bound) (by linarith) (by norm_num; linarith)
    ((abs_add_le _ _).trans (by linarith [hx i, hx j]))
  have pair_mag (i j : Fin 4) : |value (Wasm.IEEE64.add (x i) (x j))| ≤ 3*bound := by
    have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ (2*bound) (pair i j).2
      ((abs_add_le _ _).trans (by linarith [hx i, hx j]))
    have hh := mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ bound)
    nlinarith only [hm, hh, hb]
  have ht := F64ArithmeticBounds.add_error _ _ (pair 0 1).1 (pair 2 3).1
    (6*bound) (by linarith) (by norm_num; linarith)
    ((abs_add_le _ _).trans (by linarith [pair_mag 0 1, pair_mag 2 3]))
  have htmag : |value (Wasm.IEEE64.add (Wasm.IEEE64.add (x 0) (x 1))
      (Wasm.IEEE64.add (x 2) (x 3)))| ≤ 7*bound := by
    have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ (6*bound) ht.2
      ((abs_add_le _ _).trans (by linarith [pair_mag 0 1, pair_mag 2 3]))
    have hh := mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ bound)
    nlinarith only [hm, hh, hb]
  have hq := F64ArithmeticBounds.div_error _ 0x4010000000000000 ht.1
    (by unfold CodeLib.IEEE64.Finite; decide) (by decide)
    (2*bound) (by linarith) (by norm_num; linarith)
    (by rw [four_value, abs_div]; norm_num; linarith only [htmag, hb])
  rw [four_value] at hq
  have herr : |value (average (x 0) (x 1) (x 2) (x 3)) -
      Real.mean (fun i => value (x i))| ≤ 5 * bound * arithmeticEpsilon := by
    have h01 := abs_le.mp (pair 0 1).2
    have h23 := abs_le.mp (pair 2 3).2
    have ht' := abs_le.mp ht.2
    have hq' := abs_le.mp hq.2
    apply abs_le.mpr
    unfold average Real.mean
    rw [sum_four]
    constructor <;> nlinarith only [h01.1, h01.2, h23.1, h23.2, ht'.1, ht'.2, hq'.1, hq'.2, hu, hb]
  refine ⟨hq.1, ?_, herr⟩
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ bound herr
    (mean_magnitude _ bound hx)
  have hh := mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ bound)
  nlinarith only [hm, hh, hb]

theorem centered_error (x : Fin 4 → UInt64)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ 4) (i : Fin 4) :
    let c := Wasm.IEEE64.sub (x i) (average (x 0) (x 1) (x 2) (x 3))
    Finite c ∧ |value c| ≤ 12 ∧
      |value c - Real.centered (fun j => value (x j)) i| ≤ 32 * arithmeticEpsilon := by
  have hm := average_error x 4 (by norm_num) (by norm_num) hf hx
  have hs := F64ArithmeticBounds.sub_error _ _ (hf i) hm.1 12 (by norm_num) (by norm_num)
    ((abs_sub _ _).trans (by linarith [hx i, hm.2.1]))
  have hc : |Real.centered (fun j => value (x j)) i| ≤ 8 := by
    exact (abs_sub _ _).trans (by linarith [hx i, mean_magnitude _ 4 hx])
  have he : |value (Wasm.IEEE64.sub (x i) (average (x 0) (x 1) (x 2) (x 3))) -
      Real.centered (fun j => value (x j)) i| ≤ 32 * arithmeticEpsilon := by
    have h1 := abs_le.mp hs.2
    have h2 := abs_le.mp hm.2.2
    apply abs_le.mpr
    unfold Real.centered
    constructor <;> linarith
  refine ⟨hs.1, ?_, he⟩
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ 8 he hc).trans
    (by norm_num [arithmeticEpsilon])

#print axioms average_error
#print axioms centered_error
end Project.LayerNorm
