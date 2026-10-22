import Library.Numerics.Float64.Bessel.BesselMillerReal
import Library.Numerics.Float64.Bessel.BesselMillerCF

/-!
The facts about `J_i(x)` for `0 < x < 2` that the backward recurrence of `jn` uses: the recurrence
`λ_i J_i = J_(i-1) + J_(i+1)` (`J_sum`), the ratio `d_i = J_(i+1)/J_(i-1) ≤ 1/5` from `i = 3` on
(`d_le5`, with `BesselMillerReal.d_le` giving `2/3` at `i = 2`), the decrease
`J_i ≤ (5/6) J_(i-1)` from `i = 2` on (`J_decr`), `J_i ≤ λ_(i+1) J_(i+1)` (`J_ratio`), and, when
`J₁ ≤ J₀ + 2^-40`, `J₂ ≤ (21/20) J₀` (`d_one`).
-/

namespace Library.Numerics.Float64.Bessel.BesselMillerFacts
open Real LeanExe.ProofKit LeanExe.ProofKit.Bessel BesselOrderN BesselRecur BesselSmallSigns
  BesselMillerReal BesselMillerCF

set_option exponentiation.threshold 2048

theorem J_sum (w : ℝ) (hw : 0 < w) (i : ℕ) (hi : 1 ≤ i) :
    lam w i * Jn i w = Jn (i - 1) w + Jn (i + 1) w := by
  have h := Jn_recur (i - 1) w hw.ne'
  rw [show i - 1 + 2 = i + 1 by omega, show i - 1 + 1 = i by omega] at h
  unfold lam
  have : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by rw [Nat.cast_sub hi]; ring
  rw [this] at h
  linarith

theorem J_ratio (w : ℝ) (hw : 0 < w) (hw2 : w ≤ 2) (i : ℕ) : Jn i w ≤ lam w (i + 1) * Jn (i + 1) w := by
  have h := J_sum w hw (i + 1) (by omega)
  rw [show i + 1 - 1 = i by omega] at h
  have := Jn_pos (i + 1 + 1) w hw hw2
  linarith

theorem J_decr (w : ℝ) (hw : 0 < w) (hw2 : w < 2) (i : ℕ) (hi : 2 ≤ i) :
    Jn i w ≤ 5 / 6 * Jn (i - 1) w := by
  have hd := d_le w hw hw2.le i hi
  have hs := J_sum w hw i (by omega)
  have hl := lam_gt w hw hw2 i (by omega)
  have hir : (2 : ℝ) ≤ i := by exact_mod_cast hi
  have hJ := Jn_pos i w hw hw2.le
  nlinarith

/-- `d_i ≤ 1/5` for `i ≥ 3`. -/
theorem d_le5 (x : ℝ) (hx : 0 < x) (hx2 : x ≤ 2) (i : ℕ) (hi : 3 ≤ i) :
    Jn (i + 1) x ≤ 1 / 5 * Jn (i - 1) x := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by ring]
  have hb1 := (Jn_bounds (m + 2) x hx.le hx2).2
  have hb2 := (Jn_bounds m x hx.le hx2).1
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hz : x ^ 2 / 4 ≤ 1 := by nlinarith
  have hz0 : 0 ≤ x ^ 2 / 4 := by positivity
  have hF : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have f1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * (((m : ℝ) + 1) * m.factorial) := by
    rw [show m + 2 = (m + 1) + 1 by ring, Nat.factorial_succ]; push_cast; rw [f1]; ring
  have f3 : ((m + 2 + 1).factorial : ℝ) =
      ((m : ℝ) + 3) * (((m : ℝ) + 2) * (((m : ℝ) + 1) * m.factorial)) := by
    rw [Nat.factorial_succ]; push_cast; rw [f2]; ring
  have hp : (x / 2) ^ (m + 2) = (x / 2) ^ m * (x ^ 2 / 4) := by rw [pow_add]; ring
  rw [f1] at hb2
  rw [f2, f3, hp] at hb1
  obtain ⟨z, hzd⟩ : ∃ z, z = x ^ 2 / 4 := ⟨_, rfl⟩
  obtain ⟨P, hPd⟩ : ∃ P, P = (x / 2) ^ m := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F, F = (m.factorial : ℝ) := ⟨_, rfl⟩
  rw [← hzd, ← hPd, ← hFd] at hb1 hb2
  rw [← hzd] at hz hz0
  rw [← hFd] at hF
  have hP : 0 < P := by rw [hPd]; positivity
  set c := (m : ℝ) with hc
  have h1 : 0 < c + 1 := by linarith
  have h2 : 0 < c + 2 := by linarith
  have h3 : 0 < c + 3 := by linarith
  have hF' : F ≠ 0 := hF.ne'
  have h1' : c + 1 ≠ 0 := h1.ne'
  have h2' : c + 2 ≠ 0 := h2.ne'
  have h3' : c + 3 ≠ 0 := h3.ne'
  have e1 : P * z * (1 / ((c + 2) * ((c + 1) * F)) + 4 / 3 * z / ((c + 3) * ((c + 2) * ((c + 1) * F)))) =
      P * (z * (3 * (c + 3) + 4 * z) * 5) / (15 * (c + 1) * (c + 2) * (c + 3) * F) := by
    field_simp <;> ring
  have e2 : 1 / 5 * (P * (1 / F - 4 / 3 * z / ((c + 1) * F))) =
      P * ((c + 2) * (c + 3) * (3 * (c + 1) - 4 * z)) / (15 * (c + 1) * (c + 2) * (c + 3) * F) := by
    field_simp <;> ring
  have poly : z * (3 * (c + 3) + 4 * z) * 5 ≤ (c + 2) * (c + 3) * (3 * (c + 1) - 4 * z) := by
    have hc0 : 0 ≤ c := by linarith
    have hm' : 0 ≤ c - 2 := by linarith
    have hz' : 0 ≤ 1 - z := by linarith
    nlinarith [mul_nonneg (mul_nonneg hm' hc0) hc0, mul_nonneg hm' hc0, mul_nonneg (mul_nonneg hz' hc0) hc0,
      mul_nonneg hz' hc0, mul_nonneg hz' hz0]
  have hD : 0 < 15 * (c + 1) * (c + 2) * (c + 3) * F := by positivity
  have hle : P * (z * (3 * (c + 3) + 4 * z) * 5) / (15 * (c + 1) * (c + 2) * (c + 3) * F) ≤
      P * ((c + 2) * (c + 3) * (3 * (c + 1) - 4 * z)) / (15 * (c + 1) * (c + 2) * (c + 3) * F) := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact mul_le_mul_of_nonneg_left poly hP.le
  calc Jn (m + 2) x ≤ _ := hb1
    _ = _ := e1
    _ ≤ _ := hle
    _ = 1 / 5 * (P * (1 / F - 4 / 3 * z / ((c + 1) * F))) := e2.symm
    _ ≤ 1 / 5 * Jn m x := mul_le_mul_of_nonneg_left hb2 (by norm_num)

/-- `J₂ ≤ (21/20) J₀` when `J₁ ≤ J₀ + 2^-40`, for `0 < x < 2`. -/
theorem d_one (w : ℝ) (hw : 0 < w) (hw2 : w < 2) (h : Jn 1 w ≤ Jn 0 w + 1 / 2 ^ 40) :
    Jn 2 w ≤ 21 / 20 * Jn 0 w := by
  have hJ0 : 1 / 5 ≤ Jn 0 w := by
    rw [Jn_zero]; exact LeanExe.ProofKit.BesselModulus.J0_small w (by rw [abs_of_pos hw]; exact hw2.le)
  rcases le_or_gt 1 w with h1 | h1
  · have h0 := Jn_recur 0 w hw.ne'
    norm_num at h0
    have h2w : 2 / w ≤ 2 := by rw [div_le_iff₀ hw]; linarith
    have h3 : 2 / w * Jn 1 w ≤ 2 / w * (Jn 0 w + 1 / 2 ^ 40) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h4 : 2 / w * (Jn 0 w + 1 / 2 ^ 40) ≤ 2 * (Jn 0 w + 1 / 2 ^ 40) :=
      mul_le_mul_of_nonneg_right h2w (by linarith)
    linarith
  · have hb := Jn_le 2 (by norm_num) w hw.le hw2.le
    have : (w / 2) ^ 2 / ((2 : ℕ).factorial : ℝ) ≤ 1 / 8 := by
      rw [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num [Nat.factorial]]
      nlinarith
    nlinarith

#print axioms J_decr
#print axioms d_le5
#print axioms d_one

end Library.Numerics.Float64.Bessel.BesselMillerFacts
