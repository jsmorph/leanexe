import Verified.Examples.BesselMillerFacts
import Verified.Examples.BesselMillerLast
import Verified.Examples.BesselModSmall

/-!
The forward recurrence 10.6.1 from `Y₀` and `Y₁` below 2, on the reals.  For `0 < x < 2`,
`J_k > 0 > Y_k` for `k ≥ 1`, so the kernel `kern m n = (π x/2)(Y_m J_n - J_m Y_n)` of
`BesselRecur` lies from 0 to `(π x/2) J_m |Y_n|` for `1 ≤ m ≤ n` (`kern_pos`, `kern_upper`): it
starts at 0 and 1 and grows, since `λ_k = 2k/x ≥ 2` from `k = 2` on.  The error of a perturbed
sequence at `n` is then `e₂ K₁(n) - e₁ K₂(n) + Σ_(1 ≤ k ≤ n - 2) δ_k K_(k+1)(n)` (`shift_formula`,
from `BesselRecur.error_formula` and `kern_first`), and each term is at most `|Y_n|` times a
quantity of order one.  `a1_bounds` gives `π J₁ |Y₁| ≤ 2` and `(π x/2) J₁ |Y₁| ≤ 1` from the series
of `J₁` and `Y₁` and `log v ≥ 1 - 1/v` for `v = x/2`; with the cross product the second gives
`|Y₁| ≤ |Y₂|`, and the recurrence then makes `|Y_k|` nondecreasing from `k = 1` (`g_mono`).  The
products `s_j = (π x/2) J_(j+1) |Y_j|` satisfy `s_j ≤ ρ (1 + s_(j-1))` for `J_(j+1) ≤ ρ J_(j-1)`,
which gives `s₁ ≤ 5/6`, `s₂ ≤ 11/9`, and `s_j ≤ 4/9` from `j = 3` (`s_bounds`).  `small_error`
joins these: floats that start within `11 u M₀` and `12 u M₁` of `Y₀` and `Y₁` and whose steps
each add at most `u (3.01 λ_(k+1) |f_(k+1)| + |f_k|) + 2^-1070` stay within `(250 + 12 n) u |Y_n|`
of `Y_n` for `2 ≤ n ≤ N ≤ 2^31`.
-/

namespace Verified.Examples.BesselYnSmallReal
open Real Finset CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.EntireSeries
  LeanExe.ProofKit.Bessel PolyBound BesselOrderN BesselRecur BesselSmallSigns

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 4096

/-- The recurrence in the first index of the kernel at index 2. -/
theorem kern_first (w : ℝ) (hw : w ≠ 0) (n : ℕ) :
    kern w 2 n = lam w 1 * kern w 1 n - kern w 0 n := by
  have hY : Yn w 2 = 2 * ((0 : ℕ) + 1) / w * Yn w 1 - Yn w 0 := Yn_recur w 0
  have hJ : Jn 2 w = 2 * ((0 : ℕ) + 1) / w * Jn 1 w - Jn 0 w := Jn_recur 0 w hw
  simp only [kern, lam]
  rw [hY, hJ]
  push_cast
  ring

/-- **The error from the indices 1 and 2.** -/
theorem shift_formula (w : ℝ) (hw : w ≠ 0) (e δ : ℕ → ℝ)
    (he : ∀ k, e (k + 2) = lam w (k + 1) * e (k + 1) - e k + δ k) (n : ℕ) (hn : 1 ≤ n) :
    e n = e 2 * kern w 1 n - e 1 * kern w 2 n +
      ∑ k ∈ Ico 1 (n - 1), δ k * kern w (k + 1) n := by
  have h := error_formula w hw e δ he n
  unfold resp at h
  have h2 := he 0
  simp only [zero_add] at h2
  have hk := kern_first w hw n
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hb : kern w 2 1 = -1 := kern_back w hw 1
    rw [show (1 : ℕ) - 1 = 0 from rfl, Ico_eq_empty_of_le (Nat.zero_le 1), sum_empty, add_zero,
      kern_self, hb]
    ring
  · have hs : ∑ k ∈ range (n - 1), δ k * kern w (k + 1) n =
        δ 0 * kern w 1 n + ∑ k ∈ Ico 1 (n - 1), δ k * kern w (k + 1) n := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
    rw [hs] at h
    rw [h]
    linear_combination (-kern w 1 n) * h2 + e 1 * hk

/-- **The kernels from index 1 on** are nonnegative and nondecreasing in `n`. -/
theorem kern_pos (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) (m : ℕ) (hm : 1 ≤ m) :
    ∀ j : ℕ, 0 ≤ kern w m (m + j) ∧ kern w m (m + j) ≤ kern w m (m + j + 1) := by
  intro j
  induction j with
  | zero =>
    rw [add_zero, kern_self, kern_succ w hw0.ne']
    norm_num
  | succ j ih =>
    have hr := kern_recur w hw0.ne' m (m + j)
    have hl : 2 ≤ lam w (m + j + 1) := by
      have := BesselMillerCF.lam_gt w hw0 hw2 (m + j + 1) (by omega)
      have h2 : (2 : ℝ) ≤ ((m + j + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m + j + 1 by omega)
      linarith
    rw [show m + (j + 1) = m + j + 1 by ring, show m + j + 1 + 1 = m + j + 2 by ring, hr]
    refine ⟨by linarith [ih.1, ih.2], ?_⟩
    nlinarith [ih.1, ih.2]

/-- **The kernels from index 1 on** are at most `(π x/2) J_m |Y_n|`. -/
theorem kern_upper (w : ℝ) (hw0 : 0 < w) (hw2 : w ≤ 2) (m n : ℕ) (hm : 1 ≤ m) :
    kern w m n ≤ π * w / 2 * Jn m w * -Yn w n := by
  have hY := Y_neg w hw0 hw2 m hm
  have hJ := Jn_pos n w hw0 hw2
  have hP : 0 < π * w / 2 := by positivity
  simp only [kern]
  have : Yn w m * Jn n w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hY.le hJ.le
  nlinarith

/-- The kernel at `n ≥ m ≥ 1`, between 0 and `(π x/2) J_m |Y_n|`. -/
theorem kern_bounds (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    0 ≤ kern w m n ∧ kern w m n ≤ π * w / 2 * Jn m w * -Yn w n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
  exact ⟨(kern_pos w hw0 hw2 m hm j).1, kern_upper w hw0 hw2.le m (m + j) hm⟩

set_option maxHeartbeats 1000000 in
/-- **`π J₁ |Y₁| ≤ 2` and `(π x/2) J₁ |Y₁| ≤ 1`** for `0 < x < 2`. -/
theorem a1_bounds (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) :
    π * Jn 1 w * -Yn w 1 ≤ 2 ∧ π * w / 2 * Jn 1 w * -Yn w 1 ≤ 1 := by
  rw [Jn_one, Yn_one]
  obtain ⟨v, hv⟩ : ∃ v, v = w / 2 := ⟨_, rfl⟩
  have hw : w = 2 * v := by rw [hv]; ring
  have hv0 : 0 < v := by rw [hv]; positivity
  have hv1 : v < 1 := by rw [hv]; linarith
  obtain ⟨z, hz⟩ : ∃ z, z = v ^ 2 := ⟨_, rfl⟩
  have hz4 : w ^ 2 / 4 = z := by rw [hz, hw]; ring
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hz1 : z ≤ 1 := by rw [hz]; nlinarith
  have hza : |z| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have ha := a1_remainder z hza 2 (by norm_num)
  rw [a1_list2, abs_a1_2, abs_of_nonneg hz0] at ha
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat,
    mul_zero, add_zero] at ha
  have hc := c1_remainder z hza 3 (by norm_num)
  rw [c1_list3, abs_c1_3, abs_of_nonneg hz0] at hc
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat,
    mul_zero, add_zero] at hc
  obtain ⟨A, hA⟩ : ∃ A, A = psum a1 z := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = psum c1 z := ⟨_, rfl⟩
  rw [← hA] at ha
  rw [← hC] at hc
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log v + eulerMascheroniConstant := ⟨_, rfl⟩
  have hJ1 : J1 w = v * A := by rw [J1, hz4, ← hA, ← hv]
  have hY1 : Y1 w = 2 / π * L * (v * A) - 2 / (π * w) - w / (2 * π) * C := by
    rw [Y1, hJ1, hz4, ← hC, ← hv, ← hL]
  have hAu : A ≤ 1 - z / 3 := by
    have := (abs_le.mp ha).2
    nlinarith
  have hAl : 1 / 3 ≤ A := by
    have := (abs_le.mp ha).1
    nlinarith
  have hzC : 1 + z * C ≤ 5 / 4 := by
    have h := (abs_le.mp hc).2
    have h1 : z * C ≤ z * (1 + z * (-5 / 4 + z * (5 / 18))) + z * (2 * (47 / 1728) * z ^ 3) := by
      have := mul_le_mul_of_nonneg_left (show C ≤ 1 + z * (-5 / 4 + z * (5 / 18)) +
        2 * (47 / 1728) * z ^ 3 by linarith) hz0
      linarith
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1), mul_nonneg (mul_nonneg hz0 hz0)
      (sub_nonneg.mpr hz1), sq_nonneg (z - 2 / 5)]
  have hzC0 : 0 ≤ 1 + z * C := by
    have h := (abs_le.mp hc).1
    have h1 : z * (1 + z * (-5 / 4 + z * (5 / 18))) - z * (2 * (47 / 1728) * z ^ 3) ≤ z * C := by
      have := mul_le_mul_of_nonneg_left (show 1 + z * (-5 / 4 + z * (5 / 18)) -
        2 * (47 / 1728) * z ^ 3 ≤ C by linarith) hz0
      linarith
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1), mul_nonneg (mul_nonneg hz0 hz0)
      (sub_nonneg.mpr hz1)]
  have hlog := Real.one_sub_inv_le_log_of_pos hv0
  have hγ := BesselModSmall.gamma_ge
  have hpi := Real.pi_pos
  -- `(π x/2) J₁ |Y₁| = v Q` and `π J₁ |Y₁| = Q`
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = A * (1 + z * C) - 2 * z * L * A ^ 2 := ⟨_, rfl⟩
  have e1 : π * w / 2 * J1 w * -Y1 w = v * Q := by
    rw [hY1, hJ1, hQ, hz, hw]
    field_simp
    ring
  have e2 : π * J1 w * -Y1 w = Q := by
    rw [hY1, hJ1, hQ, hz, hw]
    field_simp
    ring
  -- the term in `L`, at most `2 v - 3.15 v²`, and at most 0 when `L ≥ 0`
  have hT : -(2 * z * L * A ^ 2) ≤ max 0 (2 * v - 315 / 100 * v ^ 2) := by
    by_cases hL0 : 0 ≤ L
    · have : 0 ≤ 2 * z * L * A ^ 2 := by positivity
      exact le_trans (by linarith) (le_max_left _ _)
    · push Not at hL0
      have hA2 : A ^ 2 ≤ 1 := by nlinarith
      have h1 : -(2 * z * L * A ^ 2) ≤ 2 * z * -L := by
        have : 0 ≤ 2 * z * -L := by nlinarith
        nlinarith
      have h2 : -L ≤ 1 / v - 1575 / 1000 := by
        rw [inv_eq_one_div] at hlog
        linarith
      have h3 : 2 * z * -L ≤ 2 * z * (1 / v - 1575 / 1000) := by nlinarith
      have h4 : 2 * z * (1 / v - 1575 / 1000) = 2 * v - 315 / 100 * v ^ 2 := by
        rw [hz]
        field_simp
        ring
      exact le_trans (by linarith) (le_max_right _ _)
  have hmax : max 0 (2 * v - 315 / 100 * v ^ 2) ≤ 32 / 100 := by
    apply max_le (by norm_num)
    nlinarith [sq_nonneg (v - 100 / 315)]
  have hAC : A * (1 + z * C) ≤ 5 / 4 * (1 - z / 3) := by
    calc A * (1 + z * C) ≤ (1 - z / 3) * (1 + z * C) := mul_le_mul_of_nonneg_right hAu hzC0
      _ ≤ (1 - z / 3) * (5 / 4) := mul_le_mul_of_nonneg_left hzC (by linarith)
      _ = 5 / 4 * (1 - z / 3) := by ring
  refine ⟨?_, ?_⟩
  · rw [e2, hQ]
    have : 5 / 4 * (1 - z / 3) ≤ 5 / 4 := by nlinarith
    linarith
  · rw [e1, hQ]
    have hv3 : v * (1 - z / 3) ≤ 2 / 3 := by
      rw [hz]; nlinarith [sq_nonneg (1 - v), mul_nonneg (sq_nonneg (1 - v)) hv0.le]
    by_cases h7 : 7 / 10 ≤ v
    · -- `L > 0`
      have hL0 : 0 ≤ L := by
        have : -(3 / 7) ≤ 1 - v⁻¹ := by
          have : v⁻¹ ≤ 10 / 7 := by
            rw [inv_le_comm₀ hv0 (by norm_num)]; linarith
          linarith
        linarith
      have : 0 ≤ 2 * z * L * A ^ 2 := by positivity
      nlinarith
    · push Not at h7
      have hv7 : v * (1 - z / 3) ≤ 7 / 10 * (1 - 49 / 300) := by
        rw [hz]; nlinarith [sq_nonneg (v - 7 / 10), mul_pos hv0 hv0]
      have hm : v * max 0 (2 * v - 315 / 100 * v ^ 2) ≤ 2 / 10 := by
        rcases le_total 0 (2 * v - 315 / 100 * v ^ 2) with h | h
        · rw [max_eq_right h]
          nlinarith [sq_nonneg (v - 4 / 10), mul_pos hv0 hv0]
        · rw [max_eq_left h]; norm_num
      have hvA : v * (A * (1 + z * C)) ≤ 5 / 4 * (v * (1 - z / 3)) := by nlinarith
      have hvT : v * -(2 * z * L * A ^ 2) ≤ v * max 0 (2 * v - 315 / 100 * v ^ 2) :=
        mul_le_mul_of_nonneg_left hT hv0.le
      nlinarith

/-- `|Y_k|` is nondecreasing from `k = 1` below 2. -/
theorem g_mono (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) :
    ∀ k : ℕ, 1 ≤ k → -Yn w k ≤ -Yn w (k + 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      -- `|Y₁| ≤ |Y₂|` from the cross product and `(π x/2) J₁ |Y₁| ≤ 1`
      have hc := cross w hw0.ne' 1
      have ha := (a1_bounds w hw0 hw2).2
      have hJ1 := Jn_pos 1 w hw0 hw2.le
      have hJ2 := Jn_pos 2 w hw0 hw2.le
      have hY1 := Y_neg w hw0 hw2.le 1 le_rfl
      have hpw : 0 < π * w := by positivity
      have h1 : Jn 1 w * -Yn w 1 ≤ 2 / (π * w) := by
        rw [le_div_iff₀ hpw]
        nlinarith
      have h2 : Jn 1 w * -Yn w 2 = 2 / (π * w) + Jn 2 w * -Yn w 1 := by
        show Jn 1 w * -Yn w (1 + 1) = _
        linarith
      have h3 : Jn 1 w * -Yn w 1 ≤ Jn 1 w * -Yn w 2 := by nlinarith
      exact le_of_mul_le_mul_left h3 hJ1
    · have hih := ih (by omega)
      have hr : Yn w (j + 1 + 1) = 2 * ((j : ℝ) + 1) / w * Yn w (j + 1) - Yn w j :=
        Yn_recur w j
      have hl : 2 ≤ 2 * ((j : ℝ) + 1) / w := by
        rw [le_div_iff₀ hw0]
        have : (1 : ℝ) ≤ j := by exact_mod_cast h
        nlinarith
      have hY := Y_neg w hw0 hw2.le (j + 1) (by omega)
      rw [hr]
      nlinarith

/-- The cross product with signs: `(π x/2) J_j |Y_(j+1)| = 1 + (π x/2) J_(j+1) |Y_j|`. -/
theorem cross_s (w : ℝ) (hw0 : 0 < w) (j : ℕ) :
    π * w / 2 * Jn j w * -Yn w (j + 1) = 1 + π * w / 2 * Jn (j + 1) w * -Yn w j := by
  have hc := cross w hw0.ne' j
  have hpw : π * w ≠ 0 := by positivity
  have : Jn j w * -Yn w (j + 1) = 2 / (π * w) + Jn (j + 1) w * -Yn w j := by linarith
  calc π * w / 2 * Jn j w * -Yn w (j + 1) = π * w / 2 * (Jn j w * -Yn w (j + 1)) := by ring
    _ = π * w / 2 * (2 / (π * w) + Jn (j + 1) w * -Yn w j) := by rw [this]
    _ = 1 + π * w / 2 * Jn (j + 1) w * -Yn w j := by field_simp

/-- **The products `s_j = (π x/2) J_(j+1) |Y_j|`**: `s₁ ≤ 5/6`, `s_j ≤ 11/9` from `j = 1`, and
`s_j ≤ 4/9` from `j = 3`. -/
theorem s_bounds (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) :
    π * w / 2 * Jn 2 w * -Yn w 1 ≤ 5 / 6 ∧
      (∀ j : ℕ, 1 ≤ j → π * w / 2 * Jn (j + 1) w * -Yn w j ≤ 11 / 9) ∧
      (∀ j : ℕ, 3 ≤ j → π * w / 2 * Jn (j + 1) w * -Yn w j ≤ 4 / 9) := by
  have hP : 0 < π * w / 2 := by positivity
  have hg : ∀ j, 1 ≤ j → 0 ≤ -Yn w j := fun j hj => by
    have := Y_neg w hw0 hw2.le j hj; linarith
  -- one step: `s_j ≤ ρ (1 + s_(j-1))` for `J_(j+1) ≤ ρ J_(j-1)`
  have hstep : ∀ j ρ, 2 ≤ j → 0 ≤ ρ → Jn (j + 1) w ≤ ρ * Jn (j - 1) w →
      π * w / 2 * Jn (j + 1) w * -Yn w j ≤ ρ * (1 + π * w / 2 * Jn j w * -Yn w (j - 1)) := by
    intro j ρ hj hρ hJ
    have hc := cross_s w hw0 (j - 1)
    rw [show j - 1 + 1 = j by omega] at hc
    have hgj := hg j (by omega)
    have h1 : π * w / 2 * Jn (j + 1) w * -Yn w j ≤ π * w / 2 * (ρ * Jn (j - 1) w) * -Yn w j := by
      apply mul_le_mul_of_nonneg_right _ hgj
      exact mul_le_mul_of_nonneg_left hJ hP.le
    have e : π * w / 2 * (ρ * Jn (j - 1) w) * -Yn w j =
        ρ * (π * w / 2 * Jn (j - 1) w * -Yn w j) := by ring
    rw [e, hc] at h1
    exact h1
  have hs1 : π * w / 2 * Jn 2 w * -Yn w 1 ≤ 5 / 6 := by
    have hd := BesselMillerFacts.J_decr w hw0 hw2 2 le_rfl
    have ha := (a1_bounds w hw0 hw2).2
    have hg1 := hg 1 le_rfl
    have : π * w / 2 * Jn 2 w * -Yn w 1 ≤ π * w / 2 * (5 / 6 * Jn 1 w) * -Yn w 1 := by
      apply mul_le_mul_of_nonneg_right _ hg1
      exact mul_le_mul_of_nonneg_left hd hP.le
    nlinarith
  have hs2 : π * w / 2 * Jn 3 w * -Yn w 2 ≤ 11 / 9 := by
    have h := hstep 2 (2 / 3) le_rfl (by norm_num) (BesselMillerReal.d_le w hw0 hw2.le 2 le_rfl)
    simp only [show (2 : ℕ) - 1 = 1 from rfl] at h
    nlinarith
  have hs3 : ∀ j : ℕ, 3 ≤ j → π * w / 2 * Jn (j + 1) w * -Yn w j ≤ 4 / 9 := by
    intro j hj
    induction j with
    | zero => omega
    | succ i ih =>
      have h := hstep (i + 1) (1 / 5) (by omega) (by norm_num)
        (BesselMillerFacts.d_le5 w hw0 hw2.le (i + 1) hj)
      rw [show i + 1 - 1 = i by omega] at h
      rcases Nat.lt_or_ge i 3 with hi | hi
      · have hi2 : i = 2 := by omega
        subst hi2
        nlinarith
      · have := ih hi
        nlinarith
  refine ⟨hs1, ?_, hs3⟩
  intro j hj
  rcases Nat.lt_or_ge j 3 with h | h
  · interval_cases j
    · linarith
    · exact hs2
  · linarith [hs3 j h]

theorem a0_list2 : a0List 2 = [1, -1] := by decide +kernel

theorem abs_a0_2 : |a0 2| = 1 / 4 := by
  have : qa0 2 = 1 / 4 := by decide +kernel
  rw [a0, this]
  norm_num

theorem c0_list1 : c0List 1 = [0] := by decide +kernel

theorem abs_c0_1 : |c0 1| = 1 := by
  have : qc0 1 = 1 := by decide +kernel
  rw [c0, this]
  norm_num

/-- `0 < J₁ ≤ x/2` below 2. -/
theorem J1_le (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : 0 < Jn 1 w ∧ Jn 1 w ≤ w / 2 := by
  refine ⟨Jn_pos 1 w hw0 hw2.le, ?_⟩
  rw [Jn_one, J1]
  have hz0 : 0 ≤ w ^ 2 / 4 := by positivity
  have hz1 : w ^ 2 / 4 ≤ 1 := by nlinarith
  have ha := a1_remainder (w ^ 2 / 4) (by rw [abs_of_nonneg hz0]; exact hz1) 2 (by norm_num)
  rw [a1_list2, abs_a1_2, abs_of_nonneg hz0] at ha
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat,
    mul_zero, add_zero] at ha
  have hA : psum a1 (w ^ 2 / 4) ≤ 1 := by
    have := (abs_le.mp ha).2
    nlinarith
  have : w / 2 * psum a1 (w ^ 2 / 4) ≤ w / 2 * 1 := mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

/-- `|J₀| ≤ 1` and `|Y₀| ≤ (2/π)(2/x - 1/3 + x²/2)` below 2. -/
theorem j0y0_bounds (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) :
    |J0 w| ≤ 1 ∧ |Y0 w| ≤ 2 / π * (2 / w - 1 / 3 + w ^ 2 / 2) := by
  have hz0 : 0 ≤ w ^ 2 / 4 := by positivity
  have hz1 : w ^ 2 / 4 ≤ 1 := by nlinarith
  have hza : |w ^ 2 / 4| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have ha := a0_remainder (w ^ 2 / 4) hza 2 (by norm_num)
  rw [a0_list2, abs_a0_2, abs_of_nonneg hz0] at ha
  simp only [eval_cons, eval_nil, Rat.cast_one, Rat.cast_neg, mul_zero, add_zero] at ha
  have hc := c0_remainder (w ^ 2 / 4) hza 1 (by norm_num)
  rw [c0_list1, abs_c0_1, abs_of_nonneg hz0] at hc
  simp only [eval_cons, eval_nil, Rat.cast_zero, mul_zero, add_zero, pow_one, sub_zero] at hc
  have hJ0 : |J0 w| ≤ 1 := by
    unfold J0
    rw [abs_le]
    constructor <;> nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2]
  refine ⟨hJ0, ?_⟩
  have hv0 : 0 < w / 2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hv0
  have hlog0 : Real.log (w / 2) ≤ 0 := Real.log_nonpos hv0.le (by linarith)
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hγ0 := BesselModSmall.gamma_ge
  have hinv : (w / 2)⁻¹ = 2 / w := by field_simp
  rw [hinv] at hlog
  have hL : |Real.log (w / 2) + eulerMascheroniConstant| ≤ 2 / w - 1 / 3 := by
    rw [abs_le]; constructor <;> linarith
  have hC : |psum c0 (w ^ 2 / 4)| ≤ w ^ 2 / 2 := by linarith
  unfold Y0
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / π)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 := abs_add_le ((Real.log (w / 2) + eulerMascheroniConstant) * J0 w) (psum c0 (w ^ 2 / 4))
  rw [abs_mul] at h1
  have h2 : |Real.log (w / 2) + eulerMascheroniConstant| * |J0 w| ≤ 2 / w - 1 / 3 := by
    have := mul_le_mul hL hJ0 (abs_nonneg _) (by
      have : (0 : ℝ) < 2 / w - 1 / 3 := by
        rw [sub_pos, lt_div_iff₀ hw0]; linarith
      linarith)
    linarith
  linarith

theorem sqrt_le_add (a b : ℝ) : √(a ^ 2 + b ^ 2) ≤ |a| + |b| := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

/-- `(π x/2) J₁ M₀ ≤ 10` below 2. -/
theorem p2_bound (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : π * w / 2 * Jn 1 w * modn w 0 ≤ 10 := by
  obtain ⟨hJ1p, hJ1⟩ := J1_le w hw0 hw2
  obtain ⟨hJ0, hY0⟩ := j0y0_bounds w hw0 hw2
  have hM : modn w 0 ≤ 1 + 2 / π * (2 / w - 1 / 3 + w ^ 2 / 2) := by
    unfold modn
    rw [Jn_zero, Yn_zero]
    have := sqrt_le_add (J0 w) (Y0 w)
    linarith
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  have hP : 0 ≤ π * w / 2 := by positivity
  have hM0 : 0 ≤ modn w 0 := Real.sqrt_nonneg _
  calc π * w / 2 * Jn 1 w * modn w 0 ≤ π * w / 2 * (w / 2) * (1 + 2 / π * (2 / w - 1 / 3 +
        w ^ 2 / 2)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hJ1 hP) hM hM0 (by positivity)
    _ = π * w ^ 2 / 4 + (w - w ^ 2 / 6 + w ^ 4 / 4) := by field_simp; ring
    _ ≤ 10 := by
      have hw4 : w ^ 2 ≤ 4 := by nlinarith
      have h1 : π * w ^ 2 ≤ 315 / 100 * 4 := by nlinarith [sq_nonneg w]
      have h2 : w ^ 4 ≤ 16 := by nlinarith [sq_nonneg w]
      nlinarith [sq_nonneg w]

set_option maxHeartbeats 4000000 in
/-- **The forward recurrence of `yn` below 2**: floats that start within `11 u M₀` and `12 u M₁` of
`Y₀` and `Y₁` and whose steps each add at most `u (3.01 λ_(k+1) |f_(k+1)| + |f_k|) + 2^-1070` stay
within `(250 + 12 n) u |Y_n|` of `Y_n` for `2 ≤ n ≤ N ≤ 2^31`. -/
theorem small_error (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) (N : ℕ) (hN : N ≤ 2 ^ 31) (f : ℕ → ℝ)
    (h0 : |f 0 - Yn w 0| ≤ 11 * 𝐮 * modn w 0) (h1 : |f 1 - Yn w 1| ≤ 12 * 𝐮 * modn w 1)
    (hstep : ∀ k, k + 2 ≤ N → |f (k + 2) - (lam w (k + 1) * f (k + 1) - f k)| ≤
      𝐮 * (301 / 100 * lam w (k + 1) * |f (k + 1)| + |f k|) + 1 / 2 ^ 1070) :
    ∀ n, 2 ≤ n → n ≤ N → |f n - Yn w n| ≤ (250 + 12 * (n : ℝ)) * 𝐮 * -Yn w n := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  have hP0 : 0 < π * w / 2 := by positivity
  -- the errors and the step errors
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun k => f k - Yn w k := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun k => e (k + 2) - (lam w (k + 1) * e (k + 1) - e k) :=
    ⟨_, rfl⟩
  have hrec : ∀ k, e (k + 2) = lam w (k + 1) * e (k + 1) - e k + δ k := fun k => by
    rw [hδ]; ring
  have hYrec : ∀ k, Yn w (k + 2) = lam w (k + 1) * Yn w (k + 1) - Yn w k := fun k => by
    rw [Yn_recur]; unfold lam; push_cast; ring
  have hδf : ∀ k, δ k = f (k + 2) - (lam w (k + 1) * f (k + 1) - f k) := fun k => by
    rw [hδ, he]; simp only; rw [hYrec k]; ring
  have hef : ∀ k, e k = f k - Yn w k := fun k => by rw [he]
  -- facts below 2
  obtain ⟨hs1, hs, -⟩ := s_bounds w hw0 hw2
  obtain ⟨hQ1, hA1⟩ := a1_bounds w hw0 hw2
  obtain ⟨hJ1p, hJ1⟩ := J1_le w hw0 hw2
  have hp2 := p2_bound w hw0 hw2
  have hg : ∀ k, 1 ≤ k → 0 < -Yn w k := fun k hk => by
    have := Y_neg w hw0 hw2.le k hk; linarith
  have hJk : ∀ k, 1 ≤ k → 0 < Jn k w ∧ Jn k w ≤ 1 := fun k hk =>
    ⟨Jn_pos k w hw0 hw2.le, (BesselMillerLast.Jn_le_one w hw0 hw2 k hk).trans (by linarith)⟩
  have hM1 : modn w 1 ≤ Jn 1 w + -Yn w 1 := by
    unfold modn
    have := sqrt_le_add (Jn 1 w) (Yn w 1)
    rw [abs_of_pos hJ1p, abs_of_neg (show Yn w 1 < 0 by linarith [hg 1 le_rfl])] at this
    exact this
  have hM0 : |Yn w 0| ≤ modn w 0 := by
    unfold modn
    exact Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hlam1 : π * w / 2 * lam w 1 = π := by unfold lam; push_cast; field_simp
  -- the products of a step
  have hprod : ∀ k, 1 ≤ k → π * w / 2 * Jn (k + 1) w * (lam w (k + 1) * -Yn w (k + 1)) =
      1 + π * w / 2 * Jn (k + 2) w * -Yn w (k + 1) + π * w / 2 * Jn (k + 1) w * -Yn w k := by
    intro k hk
    have hc := cross_s w hw0 (k + 1)
    have hr := hYrec k
    have e3 : lam w (k + 1) * -Yn w (k + 1) = -Yn w (k + 2) + -Yn w k := by linarith
    rw [e3, mul_add, hc]
  -- `P J₁ |e₂| ≤ 189 u + 2^-1060`
  have hE1 : |e 1| ≤ 12 * 𝐮 * (Jn 1 w + -Yn w 1) := by
    rw [hef]; exact h1.trans (mul_le_mul_of_nonneg_left hM1 (by positivity))
  have hE0 : |e 0| ≤ 11 * 𝐮 * modn w 0 := by rw [hef]; exact h0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn2 hnN
  have hd0 := hstep 0 (by omega)
  simp only [zero_add] at hd0
  have hδ0 : |δ 0| ≤ 𝐮 * (301 / 100 * lam w 1 * |f 1| + |f 0|) + 1 / 2 ^ 1070 := by
    rw [hδf 0]; exact hd0
  have hf1 : |f 1| ≤ -Yn w 1 + 12 * 𝐮 * (Jn 1 w + -Yn w 1) := by
    have := abs_sub_abs_le_abs_sub (f 1) (Yn w 1)
    rw [abs_of_neg (show Yn w 1 < 0 by linarith [hg 1 le_rfl])] at this
    rw [hef] at hE1
    linarith
  have hf0 : |f 0| ≤ modn w 0 + 11 * 𝐮 * modn w 0 := by
    have := abs_sub_abs_le_abs_sub (f 0) (Yn w 0)
    rw [hef] at hE0
    linarith
  have hB1 : π * w / 2 * Jn 1 w * |e 2| ≤ 189 * 𝐮 + 1 / 2 ^ 1060 := by
    have he2 : |e 2| ≤ lam w 1 * |e 1| + |e 0| + |δ 0| := by
      have := hrec 0
      simp only [zero_add] at this
      rw [this]
      have hl : 0 ≤ lam w 1 := by unfold lam; positivity
      calc |lam w 1 * e 1 - e 0 + δ 0| ≤ |lam w 1 * e 1| + |e 0| + |δ 0| := by
            have := abs_add_le (lam w 1 * e 1 - e 0) (δ 0)
            have := abs_sub (lam w 1 * e 1) (e 0)
            linarith
        _ = lam w 1 * |e 1| + |e 0| + |δ 0| := by rw [abs_mul, abs_of_nonneg hl]
    have hP1 : 0 ≤ π * w / 2 * Jn 1 w := mul_nonneg hP0.le hJ1p.le
    have k1 : π * w / 2 * Jn 1 w * (lam w 1 * |e 1|) ≤ 12 * 𝐮 * (π + 2) := by
      have : π * w / 2 * Jn 1 w * (lam w 1 * |e 1|) = π * Jn 1 w * |e 1| := by
        calc π * w / 2 * Jn 1 w * (lam w 1 * |e 1|) = (π * w / 2 * lam w 1) * Jn 1 w * |e 1| := by
              ring
          _ = π * Jn 1 w * |e 1| := by rw [hlam1]
      rw [this]
      have h := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hpi.le hJ1p.le)
      have : π * Jn 1 w * (12 * 𝐮 * (Jn 1 w + -Yn w 1)) =
          12 * 𝐮 * (π * Jn 1 w * Jn 1 w + π * Jn 1 w * -Yn w 1) := by ring
      rw [this] at h
      have hJJ : π * Jn 1 w * Jn 1 w ≤ π := by
        have : Jn 1 w * Jn 1 w ≤ 1 := by nlinarith
        nlinarith
      have : 12 * 𝐮 * (π * Jn 1 w * Jn 1 w + π * Jn 1 w * -Yn w 1) ≤ 12 * 𝐮 * (π + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have k2 : π * w / 2 * Jn 1 w * |e 0| ≤ 110 * 𝐮 := by
      have h := mul_le_mul_of_nonneg_left hE0 hP1
      have : π * w / 2 * Jn 1 w * (11 * 𝐮 * modn w 0) =
          11 * 𝐮 * (π * w / 2 * Jn 1 w * modn w 0) := by
        ring
      rw [this] at h
      have := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 11 * 𝐮 by positivity)
      linarith
    have k3 : π * w / 2 * Jn 1 w * |δ 0| ≤ 17 * 𝐮 + 1 / 2 ^ 1060 := by
      have h := mul_le_mul_of_nonneg_left hδ0 hP1
      have hf1' : π * Jn 1 w * |f 1| ≤ 2 + 12 * 𝐮 * (π + 2) := by
        have h' := mul_le_mul_of_nonneg_left hf1 (mul_nonneg hpi.le hJ1p.le)
        have : π * Jn 1 w * (-Yn w 1 + 12 * 𝐮 * (Jn 1 w + -Yn w 1)) =
            π * Jn 1 w * -Yn w 1 + 12 * 𝐮 * (π * Jn 1 w * Jn 1 w + π * Jn 1 w * -Yn w 1) := by ring
        rw [this] at h'
        have hJJ : π * Jn 1 w * Jn 1 w ≤ π := by
          have : Jn 1 w * Jn 1 w ≤ 1 := by nlinarith
          nlinarith
        have : 12 * 𝐮 * (π * Jn 1 w * Jn 1 w + π * Jn 1 w * -Yn w 1) ≤ 12 * 𝐮 * (π + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have hf0' : π * w / 2 * Jn 1 w * |f 0| ≤ 10 + 110 * 𝐮 := by
        have h' := mul_le_mul_of_nonneg_left hf0 hP1
        have : π * w / 2 * Jn 1 w * (modn w 0 + 11 * 𝐮 * modn w 0) =
            (π * w / 2 * Jn 1 w * modn w 0) * (1 + 11 * 𝐮) := by ring
        rw [this] at h'
        have := mul_le_mul_of_nonneg_right hp2 (show 0 ≤ 1 + 11 * 𝐮 by positivity)
        linarith
      have e1 : π * w / 2 * Jn 1 w * (𝐮 * (301 / 100 * lam w 1 * |f 1| + |f 0|) + 1 / 2 ^ 1070) =
          𝐮 * (301 / 100 * (π * Jn 1 w * |f 1|) + π * w / 2 * Jn 1 w * |f 0|) +
            π * w / 2 * Jn 1 w * (1 / 2 ^ 1070) := by
        calc π * w / 2 * Jn 1 w * (𝐮 * (301 / 100 * lam w 1 * |f 1| + |f 0|) + 1 / 2 ^ 1070) =
              𝐮 * (301 / 100 * ((π * w / 2 * lam w 1) * Jn 1 w * |f 1|) +
                π * w / 2 * Jn 1 w * |f 0|) + π * w / 2 * Jn 1 w * (1 / 2 ^ 1070) := by ring
          _ = _ := by rw [hlam1]
      rw [e1] at h
      have hPJ : π * w / 2 * Jn 1 w * (1 / 2 ^ 1070) ≤ 1 / 2 ^ 1060 := by
        have : π * w / 2 * Jn 1 w ≤ 4 := by nlinarith
        have := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ 1 / 2 ^ 1070 by positivity)
        linarith [(by norm_num : (4 : ℝ) * (1 / 2 ^ 1070) ≤ 1 / 2 ^ 1060)]
      have hsmall : 𝐮 * (301 / 100 * (2 + 12 * 𝐮 * (π + 2)) + (10 + 110 * 𝐮)) ≤ 17 * 𝐮 := by
        rw [hu]; nlinarith
      have : 𝐮 * (301 / 100 * (π * Jn 1 w * |f 1|) + π * w / 2 * Jn 1 w * |f 0|) ≤
          𝐮 * (301 / 100 * (2 + 12 * 𝐮 * (π + 2)) + (10 + 110 * 𝐮)) :=
        mul_le_mul_of_nonneg_left (by linarith) hu0
      linarith
    have := mul_le_mul_of_nonneg_left he2 hP1
    have hsum : π * w / 2 * Jn 1 w * (lam w 1 * |e 1| + |e 0| + |δ 0|) =
        π * w / 2 * Jn 1 w * (lam w 1 * |e 1|) + π * w / 2 * Jn 1 w * |e 0| +
          π * w / 2 * Jn 1 w * |δ 0| := by ring
    rw [hsum] at this
    have : 12 * 𝐮 * (π + 2) ≤ 62 * 𝐮 := by nlinarith
    linarith
  -- `P J₂ |e₁| ≤ 48 u`
  have hB2 : π * w / 2 * Jn 2 w * |e 1| ≤ 48 * 𝐮 := by
    have h := mul_le_mul_of_nonneg_left hE1 (mul_nonneg hP0.le (hJk 2 (by norm_num)).1.le)
    have : π * w / 2 * Jn 2 w * (12 * 𝐮 * (Jn 1 w + -Yn w 1)) =
        12 * 𝐮 * (π * w / 2 * Jn 2 w * Jn 1 w + π * w / 2 * Jn 2 w * -Yn w 1) := by ring
    rw [this] at h
    have hJJ : π * w / 2 * Jn 2 w * Jn 1 w ≤ π := by
      obtain ⟨a, b⟩ := hJk 2 (by norm_num)
      have : Jn 2 w * Jn 1 w ≤ 1 := by nlinarith
      have : π * w / 2 ≤ π := by nlinarith
      nlinarith
    have : 12 * 𝐮 * (π * w / 2 * Jn 2 w * Jn 1 w + π * w / 2 * Jn 2 w * -Yn w 1) ≤
        12 * 𝐮 * (π + 5 / 6) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  -- the steps from `k = 1` on
  have hB3 : ∀ k ∈ Ico 1 (n - 1), π * w / 2 * Jn (k + 1) w * |δ k| ≤
      117 / 10 * 𝐮 + 1 / 2 ^ 1060 := by
    intro k hk
    rw [mem_Ico] at hk
    have hk2 : k + 2 ≤ n := by omega
    have hd := hstep k (by omega)
    rw [← hδf k] at hd
    have hJ := hJk (k + 1) (by omega)
    have hPJ : 0 ≤ π * w / 2 * Jn (k + 1) w := mul_nonneg hP0.le hJ.1.le
    -- `|f_(k+1)| ≤ (1 + 2^-18) |Y_(k+1)|`
    have hsmallE : ∀ j, 2 ≤ j → j < n → |f j| ≤ (1 + 1 / 2 ^ 18) * -Yn w j := by
      intro j hj hjn
      have hb := ih j hjn hj (by omega)
      have hgj := hg j (by omega)
      have hj31 : (j : ℝ) ≤ 2 ^ 31 := by exact_mod_cast (show j ≤ 2 ^ 31 by omega)
      have hc : (250 + 12 * (j : ℝ)) * 𝐮 ≤ 1 / 2 ^ 18 := by rw [hu]; nlinarith
      have := abs_sub_abs_le_abs_sub (f j) (Yn w j)
      rw [abs_of_neg (show Yn w j < 0 by linarith)] at this
      have : (250 + 12 * (j : ℝ)) * 𝐮 * -Yn w j ≤ 1 / 2 ^ 18 * -Yn w j :=
        mul_le_mul_of_nonneg_right hc hgj.le
      linarith
    have hfk1 := hsmallE (k + 1) (by omega) (by omega)
    have hfk : π * w / 2 * Jn (k + 1) w * |f k| ≤ (1 + 1 / 2 ^ 18) * (11 / 9) + 12 * 𝐮 * 4 := by
      rcases Nat.lt_or_ge k 2 with hk1 | hk1
      · have hk1' : k = 1 := by omega
        subst hk1'
        have h := mul_le_mul_of_nonneg_left hf1 hPJ
        have : π * w / 2 * Jn (1 + 1) w * (-Yn w 1 + 12 * 𝐮 * (Jn 1 w + -Yn w 1)) =
            π * w / 2 * Jn 2 w * -Yn w 1 + 12 * 𝐮 * (π * w / 2 * Jn 2 w * Jn 1 w +
              π * w / 2 * Jn 2 w * -Yn w 1) := by ring
        rw [this] at h
        have hJJ : π * w / 2 * Jn 2 w * Jn 1 w ≤ π := by
          obtain ⟨a, b⟩ := hJk 2 (by norm_num)
          have : Jn 2 w * Jn 1 w ≤ 1 := by nlinarith
          have : π * w / 2 ≤ π := by nlinarith
          nlinarith
        have : 12 * 𝐮 * (π * w / 2 * Jn 2 w * Jn 1 w + π * w / 2 * Jn 2 w * -Yn w 1) ≤
            12 * 𝐮 * 4 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have : π * w / 2 * Jn 2 w * -Yn w 1 ≤ (1 + 1 / 2 ^ 18) * (11 / 9) := by
          linarith [(by norm_num : (5 : ℝ) / 6 ≤ (1 + 1 / 2 ^ 18) * (11 / 9))]
        linarith
      · have h := mul_le_mul_of_nonneg_left (hsmallE k hk1 (by omega)) hPJ
        have hsk := hs k (by omega)
        have : π * w / 2 * Jn (k + 1) w * ((1 + 1 / 2 ^ 18) * -Yn w k) =
            (1 + 1 / 2 ^ 18) * (π * w / 2 * Jn (k + 1) w * -Yn w k) := by ring
        rw [this] at h
        have := mul_le_mul_of_nonneg_left hsk (show (0 : ℝ) ≤ 1 + 1 / 2 ^ 18 by positivity)
        have : (0 : ℝ) ≤ 12 * 𝐮 * 4 := by positivity
        linarith
    have hfk1' : π * w / 2 * Jn (k + 1) w * (lam w (k + 1) * |f (k + 1)|) ≤
        (1 + 1 / 2 ^ 18) * (1 + 11 / 9 + 11 / 9) := by
      have hl : 0 ≤ lam w (k + 1) := by unfold lam; positivity
      have h := mul_le_mul_of_nonneg_left hfk1 (mul_nonneg hPJ hl)
      have hp := hprod k (by omega)
      have hsk1 := hs (k + 1) (by omega)
      have hsk := hs k (by omega)
      have : π * w / 2 * Jn (k + 1) w * lam w (k + 1) * ((1 + 1 / 2 ^ 18) * -Yn w (k + 1)) =
          (1 + 1 / 2 ^ 18) * (π * w / 2 * Jn (k + 1) w * (lam w (k + 1) * -Yn w (k + 1))) := by
        ring
      rw [this, hp] at h
      have : π * w / 2 * Jn (k + 1) w * (lam w (k + 1) * |f (k + 1)|) =
          π * w / 2 * Jn (k + 1) w * lam w (k + 1) * |f (k + 1)| := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left (show 1 + π * w / 2 * Jn (k + 1 + 1) w * -Yn w (k + 1) +
        π * w / 2 * Jn (k + 1) w * -Yn w k ≤ 1 + 11 / 9 + 11 / 9 by linarith)
        (show (0 : ℝ) ≤ 1 + 1 / 2 ^ 18 by positivity)
      linarith
    have h := mul_le_mul_of_nonneg_left hd hPJ
    have e1 : π * w / 2 * Jn (k + 1) w * (𝐮 * (301 / 100 * lam w (k + 1) * |f (k + 1)| + |f k|) +
        1 / 2 ^ 1070) = 𝐮 * (301 / 100 * (π * w / 2 * Jn (k + 1) w * (lam w (k + 1) *
          |f (k + 1)|)) + π * w / 2 * Jn (k + 1) w * |f k|) +
          π * w / 2 * Jn (k + 1) w * (1 / 2 ^ 1070) := by ring
    rw [e1] at h
    have hPJ' : π * w / 2 * Jn (k + 1) w * (1 / 2 ^ 1070) ≤ 1 / 2 ^ 1060 := by
      have : π * w / 2 * Jn (k + 1) w ≤ 4 := by nlinarith
      have := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ 1 / 2 ^ 1070 by positivity)
      linarith [(by norm_num : (4 : ℝ) * (1 / 2 ^ 1070) ≤ 1 / 2 ^ 1060)]
    have hin : 301 / 100 * (π * w / 2 * Jn (k + 1) w * (lam w (k + 1) * |f (k + 1)|)) +
        π * w / 2 * Jn (k + 1) w * |f k| ≤ 117 / 10 := by
      have : 12 * 𝐮 * 4 ≤ 1 / 2 ^ 40 := by rw [hu]; norm_num
      nlinarith
    have := mul_le_mul_of_nonneg_left hin hu0
    linarith
  -- the error at `n`
  have hsf := shift_formula w hw0.ne' e δ hrec n (by omega)
  have hgn := hg n (by omega)
  obtain ⟨k10, k1n⟩ := kern_bounds w hw0 hw2 1 n le_rfl (by omega)
  obtain ⟨k20, k2n⟩ := kern_bounds w hw0 hw2 2 n (by norm_num) hn2
  have hsumk : |∑ k ∈ Ico 1 (n - 1), δ k * kern w (k + 1) n| ≤
      ∑ k ∈ Ico 1 (n - 1), -Yn w n * (117 / 10 * 𝐮 + 1 / 2 ^ 1060) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    have hk' := mem_Ico.mp hk
    obtain ⟨kk0, kkn⟩ := kern_bounds w hw0 hw2 (k + 1) n (by omega) (by omega)
    rw [abs_mul, abs_of_nonneg kk0]
    have hb := hB3 k hk
    calc |δ k| * kern w (k + 1) n ≤ |δ k| * (π * w / 2 * Jn (k + 1) w * -Yn w n) :=
          mul_le_mul_of_nonneg_left kkn (abs_nonneg _)
      _ = -Yn w n * (π * w / 2 * Jn (k + 1) w * |δ k|) := by ring
      _ ≤ -Yn w n * (117 / 10 * 𝐮 + 1 / 2 ^ 1060) := mul_le_mul_of_nonneg_left hb hgn.le
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at hsumk
  have he2 : |e 2 * kern w 1 n| ≤ -Yn w n * (189 * 𝐮 + 1 / 2 ^ 1060) := by
    rw [abs_mul, abs_of_nonneg k10]
    calc |e 2| * kern w 1 n ≤ |e 2| * (π * w / 2 * Jn 1 w * -Yn w n) :=
          mul_le_mul_of_nonneg_left k1n (abs_nonneg _)
      _ = -Yn w n * (π * w / 2 * Jn 1 w * |e 2|) := by ring
      _ ≤ -Yn w n * (189 * 𝐮 + 1 / 2 ^ 1060) := mul_le_mul_of_nonneg_left hB1 hgn.le
  have he1 : |e 1 * kern w 2 n| ≤ -Yn w n * (48 * 𝐮) := by
    rw [abs_mul, abs_of_nonneg k20]
    calc |e 1| * kern w 2 n ≤ |e 1| * (π * w / 2 * Jn 2 w * -Yn w n) :=
          mul_le_mul_of_nonneg_left k2n (abs_nonneg _)
      _ = -Yn w n * (π * w / 2 * Jn 2 w * |e 1|) := by ring
      _ ≤ -Yn w n * (48 * 𝐮) := mul_le_mul_of_nonneg_left hB2 hgn.le
  have hen : |e n| ≤ -Yn w n * (189 * 𝐮 + 1 / 2 ^ 1060) + -Yn w n * (48 * 𝐮) +
      ((n - 1 - 1 : ℕ) : ℝ) * (-Yn w n * (117 / 10 * 𝐮 + 1 / 2 ^ 1060)) := by
    rw [hsf]
    have := abs_add_le (e 2 * kern w 1 n - e 1 * kern w 2 n)
      (∑ k ∈ Ico 1 (n - 1), δ k * kern w (k + 1) n)
    have := abs_sub (e 2 * kern w 1 n) (e 1 * kern w 2 n)
    linarith
  rw [hef] at hen
  have hcast : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hen
  have hn31 : (n : ℝ) ≤ 2 ^ 31 := by exact_mod_cast (show n ≤ 2 ^ 31 by omega)
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have htiny : (n : ℝ) * (1 / 2 ^ 1060) ≤ 𝐮 := by
    calc (n : ℝ) * (1 / 2 ^ 1060) ≤ 2 ^ 31 * (1 / 2 ^ 1060) :=
          mul_le_mul_of_nonneg_right hn31 (by positivity)
      _ ≤ 𝐮 := by rw [hu]; norm_num
  have hfin : (189 * 𝐮 + 1 / 2 ^ 1060) + 48 * 𝐮 + ((n : ℝ) - 2) * (117 / 10 * 𝐮 + 1 / 2 ^ 1060) ≤
      (250 + 12 * (n : ℝ)) * 𝐮 := by
    have ht : ((n : ℝ) - 2) * (1 / 2 ^ 1060) + 1 / 2 ^ 1060 ≤ 𝐮 := by
      have : ((n : ℝ) - 2) * (1 / 2 ^ 1060) + 1 / 2 ^ 1060 ≤ (n : ℝ) * (1 / 2 ^ 1060) := by
        nlinarith
      linarith
    have e : ((n : ℝ) - 2) * (117 / 10 * 𝐮 + 1 / 2 ^ 1060) =
        117 / 10 * ((n : ℝ) * 𝐮) - 117 / 5 * 𝐮 + ((n : ℝ) - 2) * (1 / 2 ^ 1060) := by ring
    have e2 : (250 + 12 * (n : ℝ)) * 𝐮 = 250 * 𝐮 + 12 * ((n : ℝ) * 𝐮) := by ring
    have hnu : 0 ≤ (n : ℝ) * 𝐮 := by positivity
    rw [e, e2]
    linarith
  have := mul_le_mul_of_nonneg_left hfin hgn.le
  have e3 : -Yn w n * ((189 * 𝐮 + 1 / 2 ^ 1060) + 48 * 𝐮 + ((n : ℝ) - 2) * (117 / 10 * 𝐮 +
      1 / 2 ^ 1060)) = -Yn w n * (189 * 𝐮 + 1 / 2 ^ 1060) + -Yn w n * (48 * 𝐮) +
      ((n : ℝ) - 2) * (-Yn w n * (117 / 10 * 𝐮 + 1 / 2 ^ 1060)) := by ring
  rw [e3] at this
  calc |f n - Yn w n| ≤ _ := hen
    _ ≤ -Yn w n * ((250 + 12 * (n : ℝ)) * 𝐮) := this
    _ = (250 + 12 * (n : ℝ)) * 𝐮 * -Yn w n := by ring

#print axioms shift_formula
#print axioms kern_bounds
#print axioms a1_bounds
#print axioms g_mono
#print axioms s_bounds
#print axioms p2_bound
#print axioms small_error

end Verified.Examples.BesselYnSmallReal
