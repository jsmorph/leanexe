import Library.Numerics.Float64.Bessel.BesselRecur
import LeanExe.ProofKit.BesselModulus

/-!
Signs and sizes of `J_m(x)` and `Y_m(x)` for `0 < x ≤ 2`, where `z = x²/4 ≤ 1`.  The series of
`J_m` in `z` has coefficients whose ratios are at most `1/4` from the second on, so
`|S_m(z) - 1/m!| ≤ (4/3) z/(m + 1)!` for `S_m = psum (an m)` (`series_bound`), and `J_m > 0`
(`Jn_pos`).  `Y₁ < 0` on `(0, 2]`: up to 1 from `BesselModulus.Y1_small`, and from 1 to 2 from the
definition of `Y₁` with `γ < 2/3`, `J₁ ≥ 0`, the remainders of `a1_remainder` and `c1_remainder`,
and a polynomial inequality (`Y1_neg`).  The cross product `J_(k+1) Y_k - J_k Y_(k+1) = 2/(π x)`
then gives `Y_(k+1) ≤ -2/(π x J_k)` for `k ≥ 1` (`Y_chain`), so `M_n ≥ 2/(π x J_(n-1))`
(`modn_ge`).
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallSigns
open Real Finset LeanExe.ProofKit LeanExe.ProofKit.EntireSeries LeanExe.ProofKit.Bessel PolyBound
  BesselOrderN BesselRecur

set_option exponentiation.threshold 2048

theorem an_zero_k (m : ℕ) : an m 0 = 1 / (m.factorial : ℝ) := by
  simp [an]

theorem abs_an_succ (m k : ℕ) :
    |an m (k + 1)| * (((k : ℝ) + 1) * ((m : ℝ) + k + 1)) = |an m k| := by
  rw [abs_an, abs_an, show m + (k + 1) = (m + k) + 1 by ring, Nat.factorial_succ (m + k),
    Nat.factorial_succ k]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((m + k).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h4 : (m : ℝ) + k + 1 ≠ 0 := by positivity
  push_cast
  field_simp <;> ring

/-- `|S_m(z) - 1/m!| ≤ (4/3) z/(m + 1)!` for `0 ≤ z ≤ 1`. -/
theorem series_bound (m : ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |psum (an m) z - 1 / (m.factorial : ℝ)| ≤ 4 / 3 * z / ((m + 1).factorial : ℝ) := by
  have h := (entire_an m).abs_sub_partial_le z 1 (1 / 4) (by norm_num) (by norm_num) (fun k hk => by
    have e := abs_an_succ m k
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hp : (4 : ℝ) ≤ ((k : ℝ) + 1) * ((m : ℝ) + k + 1) := by nlinarith
    have ha := abs_nonneg (an m (k + 1))
    rw [abs_of_nonneg hz0]
    nlinarith)
  rw [sum_range_one, pow_zero, mul_one, an_zero_k, abs_an, abs_of_nonneg hz0, pow_one] at h
  have e : 1 / ((Nat.factorial 1 : ℝ) * ((m + 1).factorial : ℝ)) * z / (1 - 1 / 4) =
      4 / 3 * z / ((m + 1).factorial : ℝ) := by
    have hf : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    simp only [Nat.factorial_one, Nat.cast_one, one_mul]
    field_simp <;> ring
  rw [e] at h
  exact h

/-- Bounds on `J_m` for `0 ≤ x ≤ 2`. -/
theorem Jn_bounds (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    (x / 2) ^ m * (1 / (m.factorial : ℝ) - 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ)) ≤
        Jn m x ∧
      Jn m x ≤ (x / 2) ^ m * (1 / (m.factorial : ℝ) + 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ)) := by
  have hz0 : 0 ≤ x ^ 2 / 4 := by positivity
  have hz1 : x ^ 2 / 4 ≤ 1 := by nlinarith
  have h := abs_le.mp (series_bound m (x ^ 2 / 4) hz0 hz1)
  have hp : 0 ≤ (x / 2) ^ m := by positivity
  unfold Jn
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith [h.1]) hp
  · exact mul_le_mul_of_nonneg_left (by linarith [h.2]) hp

/-- `J_m(x) > 0` for `0 < x ≤ 2`. -/
theorem Jn_pos (m : ℕ) (x : ℝ) (hx0 : 0 < x) (hx2 : x ≤ 2) : 0 < Jn m x := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [Jn_zero]
    have := LeanExe.ProofKit.BesselModulus.J0_small x (by rw [abs_of_pos hx0]; exact hx2)
    linarith
  · have hb := (Jn_bounds m x hx0.le hx2).1
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have hf1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast h
    have hz1 : x ^ 2 / 4 ≤ 1 := by nlinarith
    have hpos : 0 < 1 / (m.factorial : ℝ) - 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ) := by
      rw [hf1, sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact lt_of_lt_of_le (mul_pos (by positivity) hpos) hb

/-- `J_m(x) ≤ (5/3) (x/2)^m/m!` for `0 ≤ x ≤ 2`. -/
theorem Jn_le (m : ℕ) (hm1 : 1 ≤ m) (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    Jn m x ≤ 5 / 3 * ((x / 2) ^ m / (m.factorial : ℝ)) := by
  have hb := (Jn_bounds m x hx0 hx2).2
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hf1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hz1 : x ^ 2 / 4 ≤ 1 := by nlinarith
  have hz0 : 0 ≤ x ^ 2 / 4 := by positivity
  have hq : 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ) ≤ 2 / 3 * (1 / (m.factorial : ℝ)) := by
    rw [hf1, div_le_iff₀ (by positivity)]
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hf' : (m.factorial : ℝ) ≠ 0 := hf.ne'
    have e : 2 / 3 * (1 / (m.factorial : ℝ)) * (((m : ℝ) + 1) * m.factorial) = 2 / 3 * ((m : ℝ) + 1) := by
      field_simp <;> ring
    rw [e]
    nlinarith
  have hp : 0 ≤ (x / 2) ^ m := by positivity
  calc Jn m x ≤ (x / 2) ^ m * (1 / (m.factorial : ℝ) + 4 / 3 * (x ^ 2 / 4) / ((m + 1).factorial : ℝ)) := hb
    _ ≤ (x / 2) ^ m * (1 / (m.factorial : ℝ) + 2 / 3 * (1 / (m.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) hp
    _ = 5 / 3 * ((x / 2) ^ m / (m.factorial : ℝ)) := by ring

theorem c1_list3 : c1List 3 = [1, -5 / 4, 5 / 18] := by decide +kernel

theorem a1_list2 : a1List 2 = [1, -1 / 2] := by decide +kernel

theorem abs_c1_3 : |c1 3| = 47 / 1728 := by
  have : qc1 3 = -47 / 1728 := by decide +kernel
  rw [c1, this]
  norm_num

theorem abs_a1_2 : |a1 2| = 1 / 12 := by
  have : qa1 2 = 1 / 12 := by decide +kernel
  rw [a1, this]
  norm_num

/-- `Y₁ < 0` on `[1, 2]`. -/
theorem Y1_neg_mid (x : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ 2) : Y1 x < 0 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨z, hz⟩ : ∃ z, z = x ^ 2 / 4 := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hz1 : z ≤ 1 := by rw [hz]; nlinarith
  have hza : |z| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hc := c1_remainder z hza 3 (by norm_num)
  rw [c1_list3, abs_c1_3, abs_of_nonneg hz0] at hc
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat,
    mul_zero, add_zero] at hc
  have hP : -3 / 100 ≤ psum c1 z := by
    have := (abs_le.mp hc).1
    nlinarith [mul_nonneg (mul_nonneg hz0 hz0) (sub_nonneg.mpr hz1), sq_nonneg (1 - z),
      sub_nonneg.mpr hz1]
  have ha := a1_remainder z hza 2 (by norm_num)
  rw [a1_list2, abs_a1_2, abs_of_nonneg hz0] at ha
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat,
    mul_zero, add_zero] at ha
  have hA : psum a1 z ≤ 1 - z / 2 + z ^ 2 / 6 := by
    have := (abs_le.mp ha).2
    nlinarith
  have hJ1 : 0 ≤ J1 x := by
    have := LeanExe.ProofKit.BesselModulus.J1_mid x h1 h2
    linarith
  have hJ1u : J1 x ≤ x / 2 * (1 - z / 2 + z ^ 2 / 6) := by
    unfold J1
    rw [← hz]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hL : Real.log (x / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi := pi_pos
  have h3 : 2 / π * (Real.log (x / 2) + eulerMascheroniConstant) * J1 x ≤ 2 / π * (2 / 3) * J1 x := by
    refine mul_le_mul_of_nonneg_right ?_ hJ1
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : -(x / (2 * π) * psum c1 z) ≤ x / (2 * π) * (3 / 100) := by
    have := mul_le_mul_of_nonneg_left hP (show 0 ≤ x / (2 * π) by positivity)
    linarith
  have hY : Y1 x ≤ 2 / π * (2 / 3) * J1 x - 2 / (π * x) + x / (2 * π) * (3 / 100) := by
    unfold Y1
    rw [← hz]
    linarith
  have key : 8 / 3 * z * (1 - z / 2 + z ^ 2 / 6) - 2 + 4 * z * (3 / 200) < 0 := by
    nlinarith [mul_nonneg (mul_nonneg hz0 hz0) (sub_nonneg.mpr hz1), sq_nonneg (1 - z),
      sub_nonneg.mpr hz1]
  have hx2 : x ^ 2 = 4 * z := by rw [hz]; ring
  have hfin : (2 / π * (2 / 3) * J1 x - 2 / (π * x) + x / (2 * π) * (3 / 100)) * (π * x) < 0 := by
    have hx' : x ≠ 0 := hx0.ne'
    have hpi' : π ≠ 0 := hpi.ne'
    have e : (2 / π * (2 / 3) * J1 x - 2 / (π * x) + x / (2 * π) * (3 / 100)) * (π * x) =
        4 / 3 * x * J1 x - 2 + x ^ 2 * (3 / 200) := by
      field_simp <;> ring
    rw [e]
    have h5 := mul_le_mul_of_nonneg_left hJ1u (show 0 ≤ 4 / 3 * x by positivity)
    have e2 : 4 / 3 * x * (x / 2 * (1 - z / 2 + z ^ 2 / 6)) = 8 / 3 * z * (1 - z / 2 + z ^ 2 / 6) := by
      rw [show 4 / 3 * x * (x / 2 * (1 - z / 2 + z ^ 2 / 6)) =
        2 / 3 * x ^ 2 * (1 - z / 2 + z ^ 2 / 6) by ring, hx2]
      ring
    rw [hx2]
    linarith
  have hpx : 0 < π * x := by positivity
  rcases mul_neg_iff.mp hfin with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · linarith

/-- `Y₁ < 0` on `(0, 2]`. -/
theorem Y1_neg (x : ℝ) (h0 : 0 < x) (h2 : x ≤ 2) : Y1 x < 0 := by
  rcases le_or_gt x 1 with h | h
  · have := LeanExe.ProofKit.BesselModulus.Y1_small x h0 h
    have : 0 < 2 / (π * x) := by positivity
    linarith
  · exact Y1_neg_mid x h.le h2

/-- `Y_(k+1) ≤ -2/(π x J_k)` and `Y_(k+1) < 0` for `k ≥ 0` and `0 < x ≤ 2`, given `Y_k ≤ 0`. -/
theorem Y_step (x : ℝ) (h0 : 0 < x) (h2 : x ≤ 2) (k : ℕ) (hk : Yn x k ≤ 0) :
    Yn x (k + 1) ≤ -(2 / (π * x * Jn k x)) := by
  have hc := cross x h0.ne' k
  have hJk := Jn_pos k x h0 h2
  have hJk1 := Jn_pos (k + 1) x h0 h2
  have hpx : 0 < π * x := by positivity
  have hprod : Jn (k + 1) x * Yn x k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hJk1.le hk
  have e : Yn x (k + 1) = (Jn (k + 1) x * Yn x k - 2 / (π * x)) / Jn k x := by
    rw [eq_div_iff hJk.ne']
    linarith
  rw [e, show -(2 / (π * x * Jn k x)) = -(2 / (π * x)) / Jn k x by rw [neg_div, div_div]]
  exact div_le_div_of_nonneg_right (by linarith) hJk.le

/-- The signs of `Y_k` for `k ≥ 1` and `0 < x ≤ 2`. -/
theorem Y_neg (x : ℝ) (h0 : 0 < x) (h2 : x ≤ 2) : ∀ k : ℕ, 1 ≤ k → Yn x k < 0 := by
  intro k hk
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact Y1_neg x h0 h2
    · have hj := ih h
      have := Y_step x h0 h2 j hj.le
      have : 0 < 2 / (π * x * Jn j x) := by
        have := Jn_pos j x h0 h2
        positivity
      linarith

/-- `M_(k+1) ≥ 2/(π x J_k)` for `k ≥ 1` and `0 < x ≤ 2`. -/
theorem modn_ge (x : ℝ) (h0 : 0 < x) (h2 : x ≤ 2) (k : ℕ) (hk : 1 ≤ k) :
    2 / (π * x * Jn k x) ≤ modn x (k + 1) := by
  have hY := Y_step x h0 h2 k (Y_neg x h0 h2 k hk).le
  have hpos : 0 < 2 / (π * x * Jn k x) := by
    have := Jn_pos k x h0 h2
    positivity
  have hneg : Yn x (k + 1) < 0 := by linarith
  have habs : 2 / (π * x * Jn k x) ≤ |Yn x (k + 1)| := by
    rw [abs_of_neg hneg]
    linarith
  unfold modn
  exact le_trans habs (Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _)))

#print axioms series_bound
#print axioms Jn_pos
#print axioms Y1_neg
#print axioms Y_neg
#print axioms modn_ge

end Library.Numerics.Float64.Bessel.BesselSmallSigns
