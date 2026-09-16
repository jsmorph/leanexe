import Project.LayerNorm.Denominator

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem quotient_error (c d a r : ℝ) (hr : 1/1000 ≤ r) (hd : r/2 ≤ d)
    (ha : |a/r| ≤ 2) (hc : |c-a| ≤ 32*arithmeticEpsilon)
    (he : |d-r| ≤ 200000001*arithmeticEpsilon*r) :
    |c/d-a/r| ≤ 900000000*arithmeticEpsilon := by
  have rp : 0 < r := by linarith only [hr]
  have dp : 0 < d := by linarith only [hr, hd]
  have hi : c/d-a/r = ((c-a)+(a/r)*(r-d))/d := by field_simp; ring
  rw [hi, abs_div, abs_of_pos dp]
  apply (div_le_iff₀ dp).mpr
  have hterm : |(a/r)*(r-d)| ≤ 2*(200000001*arithmeticEpsilon*r) := by
    rw [abs_mul, abs_sub_comm r d]
    exact mul_le_mul ha he (abs_nonneg _) (by norm_num)
  have hn := (abs_add_le (c-a) ((a/r)*(r-d))).trans (add_le_add hc hterm)
  have hscale := mul_le_mul_of_nonneg_left hr
    (by positivity [F64ArithmeticBounds.epsilon_pos] : 0 ≤ 32000*arithmeticEpsilon)
  have hdscale := mul_le_mul_of_nonneg_left hd
    (by positivity [F64ArithmeticBounds.epsilon_pos] : 0 ≤ 900000000*arithmeticEpsilon)
  have hp := mul_pos F64ArithmeticBounds.epsilon_pos rp
  nlinarith only [hn, hscale, hdscale, hp]

theorem normalized_error (x : Fin 4 → UInt64)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ 4) (i : Fin 4) :
    let c := centeredWords x
    let d := denominator (c 0) (c 1) (c 2) (c 3)
    let q := Wasm.IEEE64.div (c i) d
    Finite q ∧ |value q| ≤ 3 ∧
      |value q - Real.normalized (1/100000) (fun j => value (x j)) i| ≤
        1000000000*arithmeticEpsilon := by
  let c := centeredWords x
  let d := denominator (c 0) (c 1) (c 2) (c 3)
  let r := Real.deviation (1/100000) (fun j => value (x j))
  let a := Real.centered (fun j => value (x j)) i
  have hc := centered_error x hf hx i
  have hd := denominator_error x hf hx
  have hr : 1/1000 ≤ r := by
    have h := Real.deviation_lower (1/100000) (fun j => value (x j))
    have hlo : (1:ℝ)/1000 ≤ Real.sqrt (1/100000) := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num
    exact hlo.trans h
  have ha := Real.normalized_magnitude (1/100000) (by norm_num) (fun j => value (x j)) i
  have hq := quotient_error (value (c i)) (value d) a r hr hd.2.2.1 ha hc.2.2 hd.2.2.2
  have bq : |value (c i)/value d| ≤ 3 :=
    (F64ArithmeticBounds.magnitude_of_error _ _ _ 2 hq ha).trans
      (by norm_num [arithmeticEpsilon])
  have d0 : Wasm.IEEE64.scaledMagnitude d ≠ 0 := by
    intro hh
    have hp := hd.2.1
    change 0 < value d at hp
    simp [value, Wasm.IEEE64.scaledValue, hh] at hp
  have ho := F64ArithmeticBounds.div_error (c i) d hc.1 hd.1 d0 3
    (by norm_num) (by norm_num) bq
  have he : |value (Wasm.IEEE64.div (c i) d) - a/r| ≤ 1000000000*arithmeticEpsilon :=
    (abs_sub_le _ _ _).trans ((add_le_add ho.2 hq).trans (by norm_num [arithmeticEpsilon]))
  refine ⟨ho.1, ?_, he⟩
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ 2 he ha).trans
    (by norm_num [arithmeticEpsilon])

#print axioms normalized_error
end Project.LayerNorm
