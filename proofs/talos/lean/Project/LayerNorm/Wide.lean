import Project.LayerNorm.Rms

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit RealNormalization

set_option exponentiation.threshold 4096

theorem centered_energy (x : Fin 4 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hRange : 504*bound^2+1 < (2:ℝ)^1022)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound) :
    (∀ i, Finite (centeredWords x i)) ∧ energy (centeredWords x) ≤ 36*bound^2 ∧
      14*(energy (centeredWords x)+1/100000) < (2:ℝ)^1022 := by
  have hMeanRange : 7*bound < (2:ℝ)^1022 := by nlinarith
  have hc (i : Fin 4) := centered_error_of_range x bound hb hMeanRange hf hx i
  have hEnergy : energy (centeredWords x) ≤ 36*bound^2 := by
    calc
      (∑ i : Fin 4, (value (centeredWords x i))^2) ≤ ∑ _ : Fin 4, (3*bound)^2 :=
        Finset.sum_le_sum (fun i _ => by
          have h := (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ 3*bound)).mpr (hc i).2.1
          simpa only [sq_abs, centeredWords] using h)
      _ = 36*bound^2 := by simp; ring
  exact ⟨fun i => (hc i).1, hEnergy, by nlinarith⟩

theorem normalized_centering_error (x : Fin 4 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hRange : 7*bound < (2:ℝ)^1022)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound) (i : Fin 4) :
    |value (centeredWords x i)/rms (centeredWords x)-
      Real.normalized (1/100000) (fun j => value (x j)) i| ≤ 16000*bound*arithmeticEpsilon := by
  let c := fun j => value (centeredWords x j)
  let a := Real.centered (fun j => value (x j))
  let r := rms (centeredWords x)
  let s := Real.deviation (1/100000) (fun j => value (x j))
  have hc (j : Fin 4) := (centered_error_of_range x bound hb hRange hf hx j).2.2
  have hError : 0 ≤ 8*bound*arithmeticEpsilon := by positivity [F64ArithmeticBounds.epsilon_pos]
  have hDistance : squaredDistance c a ≤ (16*bound*arithmeticEpsilon)^2 := by
    calc
      (∑ j : Fin 4, (c j-a j)^2) ≤ ∑ _ : Fin 4, (8*bound*arithmeticEpsilon)^2 :=
        Finset.sum_le_sum (fun j _ => by
          have h := (sq_le_sq₀ (abs_nonneg _) hError).mpr (hc j)
          simpa only [sq_abs, c, a, centeredWords] using h)
      _ = (16*bound*arithmeticEpsilon)^2 := by simp; ring
  have hs : 1/1000 ≤ s := by
    apply (show (1:ℝ)/1000 ≤ Real.sqrt (1/100000) by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num).trans
    exact Real.deviation_lower _ _
  have h := normalization_component_error c a r s (1/100000) 4 (1/1000)
    (16*bound*arithmeticEpsilon) (rms_pos _) (Real.deviation_pos _ (by norm_num) _)
    (by norm_num) (by norm_num) (by norm_num) (by positivity [F64ArithmeticBounds.epsilon_pos])
    (rms_lower _) hs (rms_energy _) (Real.centered_sumSquares _ (by norm_num) _) hDistance i
  exact h.trans_eq (by ring)

theorem normalized_error_wide (x : Fin 4 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hRange : 504*bound^2+1 < (2:ℝ)^1022)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound) (i : Fin 4) :
    let c := centeredWords x
    let q := Wasm.IEEE64.div (c i) (denominator (c 0) (c 1) (c 2) (c 3))
    Finite q ∧ |value q| ≤ 3 ∧
      |value q-Real.normalized (1/100000) (fun j => value (x j)) i| ≤
        (16000*bound+247)*arithmeticEpsilon := by
  have hc := centered_energy x bound hb hRange hf hx
  have hr := normalized_roundoff (centeredWords x) hc.1 hc.2.2 i
  have he := normalized_centering_error x bound hb (by nlinarith) hf hx i
  exact ⟨hr.1, hr.2.1, (abs_sub_le _ _ _).trans ((add_le_add hr.2.2 he).trans_eq (by ring))⟩

theorem affine_parameter_error (q g b : UInt64) (target gain error : ℝ)
    (hg0 : 0 ≤ gain) (hgMax : gain ≤ 10)
    (hq : Finite q) (hg : Finite g) (hb : Finite b)
    (bq : |value q| ≤ 3) (bg : |value g| ≤ gain) (bb : |value b| ≤ gain)
    (he : |value q-target| ≤ error) :
    let output := Wasm.IEEE64.add (Wasm.IEEE64.mul q g) b
    Finite output ∧ |value output-(target*value g+value b)| ≤
      gain*error+(7*gain+2)*arithmeticEpsilon := by
  have bm : |value q*value g| ≤ 3*gain := by
    rw [abs_mul]
    exact mul_le_mul bq bg (abs_nonneg _) (by norm_num)
  have hm := F64ArithmeticBounds.mul_error q g hq hg (3*gain+1)
    (by linarith) (by norm_num; linarith) (by linarith)
  have hmMag : |value (Wasm.IEEE64.mul q g)| ≤ 3*gain+1 := by
    have h := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hm.2 bm
    have hu : arithmeticEpsilon*(3*gain+1) ≤ 1 := by norm_num [arithmeticEpsilon]; linarith
    linarith
  have hs := F64ArithmeticBounds.add_error _ b hm.1 hb (4*gain+1)
    (by linarith) (by norm_num; linarith)
    ((abs_add_le _ _).trans (by linarith))
  have hp : |value q*value g-target*value g| ≤ gain*error := by
    rw [← sub_mul, abs_mul]
    exact (mul_le_mul he bg (abs_nonneg _) ((abs_nonneg _).trans he)).trans_eq (by ring)
  have h1 := abs_le.mp hm.2
  have h2 := abs_le.mp hs.2
  have h3 := abs_le.mp hp
  refine ⟨hs.1, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

theorem component_error_wide (x : Fin 4 → UInt64) (g b : UInt64) (bound gain : ℝ)
    (hb1 : 1 ≤ bound) (hRange : 504*bound^2+1 < (2:ℝ)^1022)
    (hg0 : 0 ≤ gain) (hgMax : gain ≤ 10)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound)
    (hg : Finite g) (hb : Finite b) (bg : |value g| ≤ gain) (bb : |value b| ≤ gain) (i : Fin 4) :
    let c := centeredWords x
    let output := affine (c i) (denominator (c 0) (c 1) (c 2) (c 3)) g b
    Finite output ∧ |value output| ≤ 3*gain+(254*gain+2)*arithmeticEpsilon ∧
      |value output-(Real.normalized (1/100000) (fun j => value (x j)) i*value g+value b)| ≤
        (16000*gain*bound+254*gain+2)*arithmeticEpsilon := by
  have hc := centered_energy x bound hb1 hRange hf hx
  have hr := normalized_roundoff (centeredWords x) hc.1 hc.2.2 i
  have ha := affine_parameter_error _ g b _ gain (247*arithmeticEpsilon) hg0 hgMax
    hr.1 hg hb hr.2.1 bg bb hr.2.2
  have hLocal : |value (affine (centeredWords x i)
      (denominator (centeredWords x 0) (centeredWords x 1) (centeredWords x 2) (centeredWords x 3)) g b)-
      (value (centeredWords x i)/rms (centeredWords x)*value g+value b)| ≤
      (254*gain+2)*arithmeticEpsilon := ha.2.trans_eq (by ring)
  have hm : |value (centeredWords x i)/rms (centeredWords x)*value g+value b| ≤ 3*gain := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have h := mul_le_mul (rms_normalized_magnitude (centeredWords x) i) bg (abs_nonneg _) (by norm_num)
    linarith
  have he := normalized_centering_error x bound hb1 (by nlinarith) hf hx i
  have hTarget : |(value (centeredWords x i)/rms (centeredWords x)*value g+value b)-
      (Real.normalized (1/100000) (fun j => value (x j)) i*value g+value b)| ≤
      16000*gain*bound*arithmeticEpsilon := by
    rw [add_sub_add_right_eq_sub, ← sub_mul, abs_mul]
    exact (mul_le_mul he bg (abs_nonneg _) (by positivity [F64ArithmeticBounds.epsilon_pos])).trans_eq (by ring)
  exact ⟨ha.1, F64ArithmeticBounds.magnitude_of_error _ _ _ _ hLocal hm,
    (abs_sub_le _ _ _).trans ((add_le_add hLocal hTarget).trans_eq (by ring))⟩

#print axioms normalized_centering_error
#print axioms normalized_error_wide
#print axioms component_error_wide
end Project.LayerNorm
