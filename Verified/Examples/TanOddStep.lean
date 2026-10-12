import Verified.Examples.TanOdd
import Verified.Examples.TanEven

/-!
The final step of the odd path of `Tan.kernelTan` below `0x3FE59428`: the result lies within one
step of `-1/tan r` when `x + y` approximates `r` within `|r| / 2 ^ 59`.  From `|x| = 0.4643` on,
`-1/tan r` lies in `[1, 2)` and the error stays below one spacing, `2 ^ -52`, on four intervals
of `|x|` with lower bounds on `tan` from the Taylor bounds of `sin` and `cos`.  Below, the error
stays below `0.74 u |tan r| ^ -1`.
-/

namespace Verified.Examples.TanOddStep

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanStep TanEven TanOdd TanPoly TrigApprox

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

/-- A lower bound on `tan a` from the Taylor bounds of `sin` and `cos`. -/
theorem tan_lower (a : ℝ) (h0 : 0 < a) (h1 : a ≤ 1) (hN : 0 ≤ a - a ^ 3 / 6 - a ^ 5 / 100) :
    (a - a ^ 3 / 6 - a ^ 5 / 100) / (1 - a ^ 2 / 2 + a ^ 4 * (5 / 96)) ≤ Real.tan a := by
  have hpi := Real.pi_gt_three
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs := Real.sin_bound (x := a) (by rw [abs_of_pos h0]; exact h1)
  have hc := Real.cos_bound (x := a) (by rw [abs_of_pos h0]; exact h1)
  rw [abs_of_pos h0] at hs hc
  have hs' := (abs_le.mp hs).1
  have hc' := (abs_le.mp hc).2
  rw [Real.tan_eq_sin_div_cos]
  have hD : 0 < 1 - a ^ 2 / 2 + a ^ 4 * (5 / 96) := by linarith
  rw [div_le_div_iff₀ hD hc0]
  have e1 : (a - a ^ 3 / 6 - a ^ 5 / 100) * Real.cos a ≤
      (a - a ^ 3 / 6 - a ^ 5 / 100) * (1 - a ^ 2 / 2 + a ^ 4 * (5 / 96)) :=
    mul_le_mul_of_nonneg_left (by linarith) hN
  have e2 : (a - a ^ 3 / 6 - a ^ 5 / 100) * (1 - a ^ 2 / 2 + a ^ 4 * (5 / 96)) ≤
      Real.sin a * (1 - a ^ 2 / 2 + a ^ 4 * (5 / 96)) :=
    mul_le_mul_of_nonneg_right (by linarith) hD.le
  linarith

theorem tan_mono (a s L : ℝ) (ha : L ≤ Real.tan a) (h0 : 0 < a) (has : a ≤ s)
    (hs : s ≤ 6745 / 10000) : L ≤ Real.tan s := by
  have hpi := Real.pi_gt_three
  rcases has.lt_or_eq with h | h
  · exact ha.trans (Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith) h).le
  · rw [← h]; exact ha

theorem tan_a1 : 4999 / 10000 ≤ Real.tan (4642 / 10000) :=
  le_trans (by norm_num) (tan_lower _ (by norm_num) (by norm_num) (by norm_num))

theorem tan_a2 : 5701 / 10000 ≤ Real.tan (5199 / 10000) :=
  le_trans (by norm_num) (tan_lower _ (by norm_num) (by norm_num) (by norm_num))

theorem tan_a3 : 6500 / 10000 ≤ Real.tan (5799 / 10000) :=
  le_trans (by norm_num) (tan_lower _ (by norm_num) (by norm_num) (by norm_num))

theorem tan_a4 : 7210 / 10000 ≤ Real.tan (6299 / 10000) :=
  le_trans (by norm_num) (tan_lower _ (by norm_num) (by norm_num) (by norm_num))

theorem even_err_le (X b : ℝ) (h0 : 0 ≤ X) (h : X ≤ b) : even_err X ≤ even_err b := by
  have h3 := pow_le_pow_left₀ h0 h 3
  have h5 := pow_le_pow_left₀ h0 h 5
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
  norm_num
  linarith

theorem err_b1 : even_err (52 / 100) ≤ 3463 / 10000 * 𝐮 := by
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
  norm_num

theorem err_b2 : even_err (58 / 100) ≤ 5211 / 10000 * 𝐮 := by
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
  norm_num

theorem err_b3 : even_err (63 / 100) ≤ 7175 / 10000 * 𝐮 := by
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
  norm_num

theorem err_b4 : even_err (67434 / 100000) ≤ 9397 / 10000 * 𝐮 := by
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
  norm_num

theorem even_err_odd (X : ℝ) (h0 : 1 / 2 ^ 70 ≤ X) (h1 : X ≤ 4643 / 10000) :
    even_err X ≤ 6 / 10 * 𝐮 * X := by
  have hX0 : 0 ≤ X := le_trans (by positivity) h0
  have h2 : X ^ 2 ≤ (4643 / 10000) ^ 2 := pow_le_pow_left₀ hX0 h1 2
  have h3 : X ^ 3 ≤ (4643 / 10000) ^ 2 * X := by
    rw [show X ^ 3 = X ^ 2 * X by ring]
    exact mul_le_mul_of_nonneg_right h2 hX0
  have h4 : X ^ 4 ≤ ((4643 / 10000) ^ 2) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h5 : X ^ 5 ≤ ((4643 / 10000) ^ 2) ^ 2 * X := by
    rw [show X ^ 5 = X ^ 4 * X by ring]
    exact mul_le_mul_of_nonneg_right h4 hX0
  unfold even_err
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl]
  norm_num at h0 h3 h5 ⊢
  linarith

/-- The error of the reciprocal: `τ` against `-1/t` when `W` approximates `t`. -/
theorem odd_close (t W τ E : ℝ) (hE : E < |t|) (hW : |W - t| ≤ E)
    (hτ : |τ + 1 / W| ≤ 𝐮 / 2 ^ 11 / |W|) :
    |τ - -1 / t| ≤ (𝐮 / 2 ^ 11 + E / |t|) / (|t| - E) := by
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) hW
  have hW0 : |t| - E ≤ |W| := by
    have := abs_sub_abs_le_abs_sub t W
    rw [abs_sub_comm] at this
    linarith
  have hWp : 0 < |W| := by linarith
  have htp : 0 < |t| := by linarith
  have hWne : W ≠ 0 := abs_pos.mp hWp
  have htne : t ≠ 0 := abs_pos.mp htp
  have hu0 : (0 : ℝ) ≤ 𝐮 / 2 ^ 11 := by rw [show 𝐮 = 1 / 2 ^ 53 from rfl]; positivity
  have h2 : 1 / t - 1 / W = (W - t) / (t * W) := by
    rw [div_sub_div _ _ htne hWne]
    ring
  have hid : τ - -1 / t = (τ + 1 / W) + (1 / t - 1 / W) := by ring
  rw [hid, h2]
  calc |τ + 1 / W + (W - t) / (t * W)| ≤ |τ + 1 / W| + |(W - t) / (t * W)| := abs_add_le _ _
    _ ≤ 𝐮 / 2 ^ 11 / |W| + E / (|t| * |W|) := by
        refine add_le_add hτ ?_
        rw [abs_div, abs_mul]
        exact div_le_div_of_nonneg_right hW (by positivity)
    _ = (𝐮 / 2 ^ 11 + E / |t|) / |W| := by ring
    _ ≤ (𝐮 / 2 ^ 11 + E / |t|) / (|t| - E) :=
        div_le_div_of_nonneg_left (add_nonneg hu0 (div_nonneg hE0 htp.le)) (by linarith) hW0

theorem frac_mono (c E Eb T L : ℝ) (hc : 0 ≤ c) (hE0 : 0 ≤ E) (hE : E ≤ Eb) (hL : L ≤ T)
    (hLE : Eb < L) : (c + E / T) / (T - E) ≤ (c + Eb / L) / (L - Eb) := by
  have hL0 : 0 < L := by linarith
  have h1 : E / T ≤ Eb / L := div_le_div₀ (by linarith) hE hL0 hL
  have h2 : (c + E / T) / (T - E) ≤ (c + Eb / L) / (T - E) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have h3 : (c + Eb / L) / (T - E) ≤ (c + Eb / L) / (L - Eb) :=
    div_le_div_of_nonneg_left (add_nonneg hc (div_nonneg (by linarith) hL0.le)) (by linarith)
      (by linarith)
  linarith

/-- The binade and sign conditions for `-1/tan r` in `[1, 2)`. -/
theorem bin_conds (τ T : ℝ) (hT : 1126 / 1000 ≤ |T|) (hT2 : |T| ≤ 19997 / 10000)
    (hd : |τ - T| < 1 / 2 ^ 52) :
    (B 1023 ≤ |T| ∧ |T| ≤ 2 * B 1023) ∧ (B 1023 ≤ |τ| ∧ |τ| ≤ 2 * B 1023) ∧ 0 < τ * T := by
  rw [B_1023]
  have h1 := abs_sub_abs_le_abs_sub τ T
  have h2 := abs_sub_abs_le_abs_sub T τ
  rw [abs_sub_comm] at h2
  have h3 : (1 : ℝ) / 2 ^ 52 ≤ 1 / 100 := by norm_num
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  have hd' := abs_lt.mp hd
  rcases le_or_gt 0 T with h | h
  · rw [abs_of_nonneg h] at hT
    have : 0 < τ := by linarith
    exact mul_pos this (by linarith)
  · rw [abs_of_neg h] at hT
    have : τ < 0 := by linarith
    exact mul_pos_of_neg_of_neg this h

/-- From `|x| = 0.4643` on: the error against `-1/tan r` stays below `2 ^ -52`. -/
theorem odd_bin (t W τ X s : ℝ) (hX0 : 4643 / 10000 ≤ X) (hX1 : X ≤ 67434 / 100000)
    (hs0 : X * (1 - 1 / 2 ^ 50) ≤ s) (hs1 : s ≤ 6745 / 10000) (ht : |t| = Real.tan s)
    (hW : |W - t| ≤ even_err X) (hτ : |τ + 1 / W| ≤ 𝐮 / 2 ^ 11 / |W|) :
    |τ - -1 / t| < 1 / 2 ^ 52 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 / 2 ^ 11 := by rw [hu]; positivity
  have hX0' : 0 ≤ X := by linarith
  have hE0 : 0 ≤ even_err X := le_trans (abs_nonneg _) hW
  -- One interval: `tan s ≥ L`, `even_err X ≤ Eb`, and the numeric check.
  have key : ∀ a b L Eb : ℝ, L ≤ Real.tan a → 0 < a → a ≤ s → X ≤ b → even_err b ≤ Eb →
      Eb < L → (𝐮 / 2 ^ 11 + Eb / L) / (L - Eb) < 1 / 2 ^ 52 → |τ - -1 / t| < 1 / 2 ^ 52 := by
    intro a b L Eb hLa ha has hXb hEb hLE hnum
    have hL : L ≤ |t| := by rw [ht]; exact tan_mono a s L hLa ha has hs1
    have hE : even_err X ≤ Eb := (even_err_le X b hX0' hXb).trans hEb
    have hc := odd_close t W τ (even_err X) (by linarith) hW hτ
    exact lt_of_le_of_lt (hc.trans (frac_mono _ _ _ _ _ hu0 hE0 hE hL hLE)) hnum
  have hs' : X - 1 / 10000 ≤ s := by
    have : X * (1 / 2 ^ 50) ≤ 1 / 10000 := by
      have : X * (1 / 2 ^ 50) ≤ 1 * (1 / 2 ^ 50) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have : (1 : ℝ) * (1 / 2 ^ 50) ≤ 1 / 10000 := by norm_num
      linarith
    linarith
  rcases le_or_gt X (52 / 100) with h1 | h1
  · exact key _ _ _ _ tan_a1 (by norm_num) (by linarith) h1 err_b1
      (by rw [hu]; norm_num) (by rw [hu]; norm_num)
  rcases le_or_gt X (58 / 100) with h2 | h2
  · exact key _ _ _ _ tan_a2 (by norm_num) (by linarith) h2 err_b2
      (by rw [hu]; norm_num) (by rw [hu]; norm_num)
  rcases le_or_gt X (63 / 100) with h3 | h3
  · exact key _ _ _ _ tan_a3 (by norm_num) (by linarith) h3 err_b3
      (by rw [hu]; norm_num) (by rw [hu]; norm_num)
  · exact key _ _ _ _ tan_a4 (by norm_num) (by linarith) hX1 err_b4
      (by rw [hu]; norm_num) (by rw [hu]; norm_num)

/-- Below `|x| = 0.4643`: the error against `-1/tan r` stays below `0.74 u` of its size. -/
theorem odd_rel (t W τ X : ℝ) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 4643 / 10000)
    (hs0 : X * (1 - 1 / 2 ^ 50) ≤ |t|) (hW : |W - t| ≤ even_err X)
    (hτ : |τ + 1 / W| ≤ 𝐮 / 2 ^ 11 / |W|) :
    |τ - -1 / t| ≤ 74 / 100 * 𝐮 * |-1 / t| := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hE := even_err_odd X hX0 hX1
  have hX0' : 0 < X := lt_of_lt_of_le (by positivity) hX0
  have htp : 0 < |t| := lt_of_lt_of_le (by
    have : (0 : ℝ) < 1 - 1 / 2 ^ 50 := by norm_num
    positivity) hs0
  have hE0 : 0 ≤ even_err X := le_trans (abs_nonneg _) hW
  have hEt : even_err X < |t| := by
    rw [hu] at hE
    have : X * (1 - 1 / 2 ^ 50) ≤ |t| := hs0
    linarith
  have hc := odd_close t W τ (even_err X) hEt hW hτ
  refine hc.trans ?_
  rw [abs_div, abs_neg, abs_one, mul_one_div, div_le_div_iff₀ (by linarith) htp,
    add_mul, div_mul_cancel₀ _ htp.ne']
  rw [hu] at hE ⊢
  linarith

/-- The correction stays below `|x| / 5`. -/
theorem corr_small (x y : UInt64) (X : ℝ) (hxf : Finite x) (hyf : Finite y)
    (hX : |value x| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 67434 / 100000)
    (hy : |value y| ≤ X / 2 ^ 52) : |value (corrW x y)| ≤ X / 5 := by
  obtain ⟨M, ⟨⟨-, he⟩, hM⟩, hMb⟩ := corr_AB x y X hxf hyf hX (by linarith) hy
  have hX0' : 0 ≤ X := le_trans (by positivity) hX0
  have h2 : X ^ 2 ≤ (67434 / 100000) ^ 2 := pow_le_pow_left₀ hX0' hX1 2
  have h3 : X ^ 3 ≤ (67434 / 100000) ^ 2 * X := by
    rw [show X ^ 3 = X ^ 2 * X by ring]
    exact mul_le_mul_of_nonneg_right h2 hX0'
  have h4 : X ^ 4 ≤ ((67434 / 100000) ^ 2) ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have h5 : X ^ 5 ≤ ((67434 / 100000) ^ 2) ^ 2 * X := by
    rw [show X ^ 5 = X ^ 4 * X by ring]
    exact mul_le_mul_of_nonneg_right h4 hX0'
  have h6 := abs_sub_abs_le_abs_sub (value (corrW x y)) (corrT (value x) (value y))
  rw [show 𝐮 = 1 / 2 ^ 53 from rfl, show η = 1 / 2 ^ 1075 from rfl] at he
  norm_num at h3 h5 he hMb hX0
  linarith

/-- The odd path below `0x3FE59428`. -/
theorem odd_within (x y : UInt64) (r X : ℝ) (hxf : Finite x) (hyf : Finite y)
    (hX : |value x| = X) (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 67434 / 100000)
    (hy : |value y| ≤ X / 2 ^ 52) (har : |value x + value y - r| ≤ |r| / 2 ^ 59) :
    F64SignedRounding.WithinSteps 1 (-1 / Real.tan r) (oddW x (corrW x y)) := by
  obtain ⟨hcf, -, hd, hr0, hr1⟩ := even_sum x y r X hxf hyf hX hX1 hy har
  have hcs := corr_small x y X hxf hyf hX hX0 hX1 hy
  obtain ⟨hof, τ, hnear, hτ⟩ := odd_spec x (corrW x y) X hxf hcf hX hX0 (by linarith) hcs
  have hpi := Real.pi_gt_three
  have hX0' : 0 ≤ X := le_trans (by positivity) hX0
  have hr6 : |r| ≤ 6745 / 10000 := by
    have : X * (1 + 1 / 2 ^ 50) ≤ 6745 / 10000 := by
      have : X * (1 / 2 ^ 50) ≤ 1 / 2 ^ 50 := by
        have := mul_le_mul_of_nonneg_right (show X ≤ 1 by linarith)
          (show (0 : ℝ) ≤ 1 / 2 ^ 50 by positivity)
        linarith
      have : (67434 / 100000 : ℝ) + 1 / 2 ^ 50 ≤ 6745 / 10000 := by norm_num
      linarith
    linarith
  have hTa := abs_tan r (by linarith)
  obtain ⟨hlo, hhi, hmid⟩ := tan_bounds |r| (abs_nonneg r) hr6
  have hnear' : ∀ v : UInt64, Finite v →
      |value (oddW x (corrW x y)) - τ| ≤ |value v - τ| := fun v _ => hnear v
  have hTabs : |-1 / Real.tan r| = 1 / |Real.tan r| := by rw [abs_div, abs_neg, abs_one]
  rcases le_or_gt (4643 / 10000) X with hbig | hsmall
  · have hclose := odd_bin (Real.tan r) _ τ X |r| hbig hX1 hr0 hr6 hTa hd hτ
    have hT1 : 5001 / 10000 ≤ |Real.tan r| := by
      rw [hTa]
      exact hmid (by
        have : X * (1 / 2 ^ 50) ≤ 1 / 10000 := by
          have := mul_le_mul_of_nonneg_right (show X ≤ 1 by linarith)
            (show (0 : ℝ) ≤ 1 / 2 ^ 50 by positivity)
          have : (1 : ℝ) * (1 / 2 ^ 50) ≤ 1 / 10000 := by norm_num
          linarith
        linarith)
    have hT2 : |Real.tan r| ≤ 8875 / 10000 := by rw [hTa]; exact hhi
    obtain ⟨hT, ht, hs⟩ := bin_conds τ (-1 / Real.tan r)
      (by
        rw [hTabs, le_div_iff₀ (by linarith)]
        linarith)
      (by
        rw [hTabs, div_le_iff₀ (by linarith)]
        linarith)
      hclose
    exact near_bin _ τ (-1 / Real.tan r) 1023 (by norm_num) (by norm_num) hof hnear' hT ht hs
      (by rw [S_1023]; exact hclose)
  · have hs0 : X * (1 - 1 / 2 ^ 50) ≤ |Real.tan r| := by rw [hTa]; linarith
    refine near_rel _ τ (-1 / Real.tan r) hof hnear' ?_ ?_
      (odd_rel (Real.tan r) _ τ X hX0 hsmall.le hs0 hd hτ)
    · rw [hTabs, le_div_iff₀ (by
        have : (0 : ℝ) < 1 - 1 / 2 ^ 50 := by norm_num
        have : 0 < X * (1 - 1 / 2 ^ 50) := by positivity
        linarith)]
      have : (1 : ℝ) / 2 ^ 1000 * (8875 / 10000) ≤ 1 := by norm_num
      have : 1 / 2 ^ 1000 * |Real.tan r| ≤ 1 / 2 ^ 1000 * (8875 / 10000) :=
        mul_le_mul_of_nonneg_left (by rw [hTa]; exact hhi) (by positivity)
      linarith
    · rw [hTabs, div_le_iff₀ (by
        have : (0 : ℝ) < 1 - 1 / 2 ^ 50 := by norm_num
        have : 0 < X * (1 - 1 / 2 ^ 50) := by positivity
        linarith)]
      have : (1 : ℝ) ≤ 2 ^ 1000 * (1 / 2 ^ 70 * (1 - 1 / 2 ^ 50)) := by norm_num
      have : 2 ^ 1000 * (1 / 2 ^ 70 * (1 - 1 / 2 ^ 50)) ≤ 2 ^ 1000 * (X * (1 - 1 / 2 ^ 50)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX0 (by norm_num)) (by positivity)
      have : 2 ^ 1000 * (X * (1 - 1 / 2 ^ 50)) ≤ 2 ^ 1000 * |Real.tan r| :=
        mul_le_mul_of_nonneg_left hs0 (by positivity)
      linarith

#print axioms odd_within

end Verified.Examples.TanOddStep
