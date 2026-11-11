import Demos.Orbit.Lambert
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The monotonicity of Izzo's time of flight and the existence and uniqueness of its root.  For
`-1 < λ < 1`, `tof_strictAntiOn` states that `tof lam` is strictly decreasing on `(-1, ∞)` (L2),
`tof_continuousOn` that it is continuous there, and `exists_unique_root` that for every `T > 0`
exactly one `x > -1` has `tof lam x = T` (L3).  The decrease on `(0, ∞)` and on `(-1, 0)` follows
from the integral representations of `Lambert.lean`, whose integrand increases with `1 - x²`, and
the two pieces join at 0 by continuity.
-/

namespace Demos.Orbit.Lambert

open Real Set Filter Topology intervalIntegral

/-! ### The integrand -/

theorem integrand_le {w1 w2 s : ℝ} (hw : w1 ≤ w2) (h2 : 0 < 1 - w2 * s ^ 2) :
    integrand w1 s ≤ integrand w2 s := by
  unfold integrand
  exact div_le_div_of_nonneg_left (sq_nonneg s) (sqrt_pos.mpr h2)
    (sqrt_le_sqrt (by nlinarith [sq_nonneg s]))

theorem integrand_lt_one {w1 w2 : ℝ} (hw : w1 < w2) (h2 : w2 < 1) :
    integrand w1 1 < integrand w2 1 := by
  unfold integrand
  simp only [one_pow, mul_one]
  exact div_lt_div_of_pos_left one_pos (sqrt_pos.mpr (by linarith))
    (sqrt_lt_sqrt (by linarith) (by linarith))

theorem continuousOn_integrand_Icc {w a : ℝ} (hw : w < 1) (ha : -1 ≤ a) (ha1 : a ≤ 1) :
    ContinuousOn (integrand w) (Icc a 1) := by
  have := continuousOn_integrand (integrand_pos_den hw ha le_rfl ha1)
  rwa [uIcc_of_le ha1] at this

/-! ### Monotonicity on each side of 0 -/

theorem tof_strictAntiOn_pos {lam : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) :
    StrictAntiOn (tof lam) (Ioi 0) := by
  intro x1 hx1 x2 hx2 hlt
  have hx1' : (0 : ℝ) < x1 := hx1
  rw [tof_pos_eq hl0 hl1 hx2, tof_pos_eq hl0 hl1 hx1']
  have hw : 1 - x2 ^ 2 < 1 - x1 ^ 2 := by nlinarith
  have hw1 : 1 - x1 ^ 2 < 1 := by nlinarith
  apply mul_lt_mul_of_pos_left _ two_pos
  apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hl1
    (continuousOn_integrand_Icc (by linarith) hl0.le hl1.le)
    (continuousOn_integrand_Icc hw1 hl0.le hl1.le)
  · intro s hs
    apply integrand_le hw.le
    have : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    rcases le_total 0 (1 - x1 ^ 2) with h | h <;> nlinarith
  · exact ⟨1, ⟨hl1.le, le_rfl⟩, integrand_lt_one hw hw1⟩

theorem tof_strictAntiOn_neg {lam : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) :
    StrictAntiOn (tof lam) (Ioo (-1) 0) := by
  intro x1 hx1 x2 hx2 hlt
  rw [tof_neg_eq hl0 hl1 hx2.1 hx2.2, tof_neg_eq hl0 hl1 hx1.1 hx1.2]
  have hw1 : 0 < 1 - x1 ^ 2 := by nlinarith [hx1.1, hx1.2]
  have hw : 1 - x1 ^ 2 < 1 - x2 ^ 2 := by nlinarith [hx1.2, hx2.2]
  have hw2 : 1 - x2 ^ 2 < 1 := by nlinarith [hx2.2]
  have hint : (∫ s in (-lam)..1, integrand (1 - x1 ^ 2) s) ≤
      ∫ s in (-lam)..1, integrand (1 - x2 ^ 2) s := by
    apply integral_mono_on (by linarith)
      ((continuousOn_integrand_Icc (by linarith) (by linarith) (by linarith)).intervalIntegrable_of_Icc
        (by linarith))
      ((continuousOn_integrand_Icc hw2 (by linarith) (by linarith)).intervalIntegrable_of_Icc
        (by linarith))
    intro s hs
    apply integrand_le hw.le
    have : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    nlinarith
  have hr1 : 0 < √(1 - x1 ^ 2) := sqrt_pos.mpr hw1
  have hr : √(1 - x1 ^ 2) < √(1 - x2 ^ 2) := sqrt_lt_sqrt hw1.le hw
  have hd : π / ((1 - x2 ^ 2) * √(1 - x2 ^ 2)) < π / ((1 - x1 ^ 2) * √(1 - x1 ^ 2)) :=
    div_lt_div_of_pos_left pi_pos (by positivity) (mul_lt_mul hw hr.le hr1 (by linarith))
  linarith

/-! ### Continuity -/

theorem tof_continuousOn_lt {lam : ℝ} : ContinuousOn (tof lam) (Ioo (-1) 1) := by
  have hc : ContinuousOn (fun x => (arccos (x * yOf lam x + lam * (1 - x ^ 2)) / √(1 - x ^ 2) -
      x + lam * yOf lam x) / (1 - x ^ 2)) (Ioo (-1) 1) := by
    have hden : ∀ x ∈ Ioo (-1 : ℝ) 1, 1 - x ^ 2 ≠ 0 := fun x hx => by
      nlinarith [hx.1, hx.2]
    have hrt : ∀ x ∈ Ioo (-1 : ℝ) 1, √(1 - x ^ 2) ≠ 0 := fun x hx =>
      (sqrt_pos.mpr (by nlinarith [hx.1, hx.2])).ne'
    unfold yOf
    apply ContinuousOn.div _ (by fun_prop) hden
    apply ContinuousOn.add _ (by fun_prop)
    apply ContinuousOn.sub _ (by fun_prop)
    apply ContinuousOn.div _ (by fun_prop) hrt
    exact (continuous_arccos.comp (by fun_prop)).continuousOn
  refine hc.congr (fun x hx => ?_)
  simp [tof, hx.2]

theorem tof_continuousOn_gt {lam : ℝ} (hl1 : lam < 1) : ContinuousOn (tof lam) (Ioi 1) := by
  have hc : ContinuousOn (fun x => ((arsinh √(x ^ 2 - 1) - arsinh (lam * √(x ^ 2 - 1))) /
      √(x ^ 2 - 1) - x + lam * yOf lam x) / (1 - x ^ 2)) (Ioi 1) := by
    have hden : ∀ x ∈ Ioi (1 : ℝ), 1 - x ^ 2 ≠ 0 := fun x hx => by
      have : (1 : ℝ) < x := hx; nlinarith
    have hrt : ∀ x ∈ Ioi (1 : ℝ), √(x ^ 2 - 1) ≠ 0 := fun x hx => by
      have : (1 : ℝ) < x := hx; exact (sqrt_pos.mpr (by nlinarith)).ne'
    unfold yOf
    apply ContinuousOn.div _ (by fun_prop) hden
    apply ContinuousOn.add _ (by fun_prop)
    apply ContinuousOn.sub _ (by fun_prop)
    apply ContinuousOn.div _ (by fun_prop) hrt
    exact ((continuous_arsinh.comp (by fun_prop)).sub
      (continuous_arsinh.comp (by fun_prop))).continuousOn
  refine hc.congr (fun x hx => ?_)
  have h1 : (1 : ℝ) < x := hx
  simp only [tof, not_lt.mpr h1.le, h1.ne', ite_false]
  rw [psi_hyperbolic hl1 h1]

/-- The integrand made continuous on the plane: the same as `integrand (1 - x²) s` when
`1 - (1 - x²) s² ≥ 1/2`. -/
noncomputable def integrandSafe (x s : ℝ) : ℝ := s ^ 2 / √(max (1 - (1 - x ^ 2) * s ^ 2) (1 / 2))

theorem continuous_integrandSafe : Continuous (Function.uncurry integrandSafe) := by
  unfold integrandSafe Function.uncurry
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  exact (sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (le_max_right _ _))).ne'

theorem tof_continuousAt_one {lam : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) :
    ContinuousAt (tof lam) 1 := by
  have hG : Continuous fun x => 2 * ∫ s in lam..1, integrandSafe x s :=
    continuous_const.mul (continuous_parametric_intervalIntegral_of_continuous'
      continuous_integrandSafe lam 1)
  apply hG.continuousAt.congr
  filter_upwards [Ioo_mem_nhds (show (0.8 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) < 1.2 by norm_num)] with x hx
  rw [tof_pos_eq hl0 hl1 (by linarith [hx.1])]
  congr 1
  apply integral_congr
  intro s hs
  rw [uIcc_of_le hl1.le] at hs
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  have hb : 1 / 2 ≤ 1 - (1 - x ^ 2) * s ^ 2 := by
    rcases le_total 0 (1 - x ^ 2) with h | h
    · nlinarith [hx.1, hx.2, sq_nonneg s]
    · nlinarith [hx.1, hx.2, sq_nonneg s]
  simp only [integrandSafe, integrand, max_eq_left hb]

theorem tof_continuousOn {lam : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) :
    ContinuousOn (tof lam) (Ioi (-1)) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rcases lt_trichotomy x 1 with h | h | h
  · exact tof_continuousOn_lt.continuousAt (isOpen_Ioo.mem_nhds ⟨hx, h⟩)
  · subst h; exact tof_continuousAt_one hl0 hl1
  · exact (tof_continuousOn_gt hl1).continuousAt (isOpen_Ioi.mem_nhds h)

/-! ### Monotonicity on `(-1, ∞)` -/

/-- A function strictly decreasing on `(a, c)` and on `(c, ∞)` and continuous at `c` is strictly
decreasing on `(a, ∞)`. -/
theorem strictAntiOn_join {f : ℝ → ℝ} {a c : ℝ} (h1 : StrictAntiOn f (Ioo a c))
    (h2 : StrictAntiOn f (Ioi c)) (hc : ContinuousAt f c) : StrictAntiOn f (Ioi a) := by
  have left : ∀ x ∈ Ioo a c, f c < f x := by
    intro x hx
    set z := (x + c) / 2
    have hxz : x < z := by simp only [z]; linarith [hx.2]
    have hzc : z < c := by simp only [z]; linarith [hx.2]
    have hz : z ∈ Ioo a c := ⟨by linarith [hx.1], hzc⟩
    have hfz : f z < f x := h1 hx hz hxz
    have hle : f c ≤ f z := by
      apply le_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio c)))
      filter_upwards [Ioo_mem_nhdsLT hzc] with u hu
      exact (h1 hz ⟨by linarith [hu.1, hz.1], hu.2⟩ hu.1).le
    linarith
  have right : ∀ y ∈ Ioi c, f y < f c := by
    intro y hy
    have hy' : c < y := hy
    set z := (c + y) / 2
    have hcz : c < z := by simp only [z]; linarith
    have hzy : z < y := by simp only [z]; linarith
    have hfz : f y < f z := h2 hcz hy hzy
    have hle : f z ≤ f c := by
      apply ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi c)))
      filter_upwards [Ioo_mem_nhdsGT hcz] with u hu
      exact (h2 hu.1 hcz hu.2).le
    linarith
  intro x hx y hy hxy
  have hx' : a < x := hx
  have hy' : a < y := hy
  rcases lt_trichotomy x c with h | h | h
  · rcases lt_trichotomy y c with k | k | k
    · exact h1 ⟨hx', h⟩ ⟨hy', k⟩ hxy
    · subst k; exact left x ⟨hx', h⟩
    · exact (right y k).trans (left x ⟨hx', h⟩)
  · subst h; exact right y hxy
  · exact h2 h (h.trans hxy) hxy

/-- **L2.**  `tof lam` is strictly decreasing on `(-1, ∞)`. -/
theorem tof_strictAntiOn {lam : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) :
    StrictAntiOn (tof lam) (Ioi (-1)) :=
  strictAntiOn_join (tof_strictAntiOn_neg hl0 hl1) (tof_strictAntiOn_pos hl0 hl1)
    ((tof_continuousOn hl0 hl1).continuousAt (isOpen_Ioi.mem_nhds (by norm_num)))

/-! ### Values far from the root -/

/-- For `x > 1`, `tof lam x ≤ 2 (1 - λ)/√(x² - 1)`. -/
theorem tof_le_of_gt {lam x : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hx : 1 < x) :
    tof lam x ≤ 2 * ((1 - lam) / √(x ^ 2 - 1)) := by
  have hk : 0 < x ^ 2 - 1 := by nlinarith
  have hr : 0 < √(x ^ 2 - 1) := sqrt_pos.mpr hk
  rw [tof_pos_eq hl0 hl1 (by linarith)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hw : 1 - x ^ 2 < 1 := by nlinarith
  calc (∫ s in lam..1, integrand (1 - x ^ 2) s) ≤ ∫ _ in lam..1, 1 / √(x ^ 2 - 1) := by
        apply integral_mono_on hl1.le
          ((continuousOn_integrand_Icc hw hl0.le hl1.le).intervalIntegrable_of_Icc hl1.le)
          intervalIntegrable_const
        intro s hs
        have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
        have hq : 0 < 1 - (1 - x ^ 2) * s ^ 2 := by nlinarith [sq_nonneg s]
        unfold integrand
        rw [div_le_div_iff₀ (sqrt_pos.mpr hq) hr]
        have h1 : s ^ 2 * √(x ^ 2 - 1) ≤ √(1 - (1 - x ^ 2) * s ^ 2) := by
          apply le_sqrt_of_sq_le
          rw [mul_pow, sq_sqrt hk.le]
          nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) hk.le]
        linarith
    _ = (1 - lam) / √(x ^ 2 - 1) := by
        rw [integral_const, smul_eq_mul]; ring

/-- Some `x > 1` has `tof lam x < T`. -/
theorem exists_tof_lt {lam T : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hT : 0 < T) :
    ∃ x, 1 < x ∧ tof lam x < T := by
  set k := 4 / T + 1
  have hk : 0 < k := by positivity
  have hx : 1 < √(1 + k ^ 2) := (lt_sqrt (by norm_num)).mpr (by nlinarith)
  refine ⟨√(1 + k ^ 2), hx, ?_⟩
  have e : √(√(1 + k ^ 2) ^ 2 - 1) = k := by
    rw [sq_sqrt (by positivity), show 1 + k ^ 2 - 1 = k ^ 2 by ring, sqrt_sq hk.le]
  have := tof_le_of_gt hl0 hl1 hx
  rw [e] at this
  calc tof lam √(1 + k ^ 2) ≤ 2 * ((1 - lam) / k) := this
    _ < T := by
      rw [mul_div_assoc', div_lt_iff₀ hk]
      simp only [k]
      field_simp
      nlinarith

/-- Some `x` in `(-1, 0)` has `T < tof lam x`. -/
theorem exists_lt_tof {lam T : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) :
    ∃ x, -1 < x ∧ x < 0 ∧ T < tof lam x := by
  set w := min (1 / 2) (1 / (|T| + 9))
  have hw0 : 0 < w := lt_min (by norm_num) (by positivity)
  have hw1 : w ≤ 1 / 2 := min_le_left _ _
  have hw2 : w ≤ 1 / (|T| + 9) := min_le_right _ _
  have hw1' : √(1 - w) < 1 := (sqrt_lt' one_pos).mpr (by linarith)
  refine ⟨-√(1 - w), ?_, ?_, ?_⟩
  · linarith
  · have : 0 < √(1 - w) := sqrt_pos.mpr (by linarith)
    linarith
  · have hx2 : 1 - (-√(1 - w)) ^ 2 = w := by
      rw [neg_sq, sq_sqrt (by linarith)]; ring
    have hlt : -√(1 - w) < 0 := by have := sqrt_pos.mpr (show 0 < 1 - w by linarith); linarith
    have hgt : -1 < -√(1 - w) := by linarith
    rw [tof_neg_eq hl0 hl1 hgt hlt, hx2]
    have hint : (∫ s in (-lam)..1, integrand w s) ≤ ∫ _ in (-lam)..1, (2 : ℝ) := by
      apply integral_mono_on (by linarith)
        ((continuousOn_integrand_Icc (by linarith) (by linarith) (by linarith)).intervalIntegrable_of_Icc
          (by linarith))
        intervalIntegrable_const
      intro s hs
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
      have hq : 1 / 2 ≤ 1 - w * s ^ 2 := by nlinarith
      unfold integrand
      rw [div_le_iff₀ (sqrt_pos.mpr (by linarith))]
      have : (1 : ℝ) / 2 ≤ √(1 - w * s ^ 2) := by
        apply le_sqrt_of_sq_le; nlinarith
      nlinarith
    rw [integral_const, smul_eq_mul] at hint
    have hsw : √w ≤ 1 := (sqrt_le_one).mpr (by linarith)
    have hsw0 : 0 < √w := sqrt_pos.mpr hw0
    have hT' : T ≤ |T| := le_abs_self T
    have hpi : 2 ≤ π := two_le_pi
    have hbig : |T| + 9 ≤ 1 / w := by
      rw [le_div_iff₀ hw0]
      have h9 : 0 < |T| + 9 := by positivity
      have := mul_le_mul_of_nonneg_left hw2 h9.le
      rw [mul_one_div_cancel h9.ne'] at this
      linarith
    have hden : w * √w ≤ w := by nlinarith
    have : 1 / w ≤ π / (w * √w) := by
      rw [div_le_div_iff₀ hw0 (by positivity)]
      nlinarith
    have hlam : 1 - -lam ≤ 2 := by linarith
    linarith

/-! ### The root -/

/-- **L3.**  For `-1 < λ < 1` and `T > 0`, exactly one `x > -1` has `tof lam x = T`. -/
theorem exists_unique_root {lam T : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hT : 0 < T) :
    ∃! x, -1 < x ∧ tof lam x = T := by
  obtain ⟨a, ha0, ha1, ha⟩ := exists_lt_tof (T := T) hl0 hl1
  obtain ⟨b, hb1, hb⟩ := exists_tof_lt hl0 hl1 hT
  have hab : a ≤ b := by linarith
  have hsub : Icc a b ⊆ Ioi (-1) := fun z hz => lt_of_lt_of_le ha0 hz.1
  obtain ⟨x, hx, hxT⟩ := intermediate_value_Icc' hab ((tof_continuousOn hl0 hl1).mono hsub)
    ⟨hb.le, ha.le⟩
  refine ⟨x, ⟨hsub hx, hxT⟩, fun z hz => ?_⟩
  exact (tof_strictAntiOn hl0 hl1).injOn hz.1 (hsub hx) (hz.2.trans hxT.symm)

/-- The root of `tof lam x = T`, for `-1 < λ < 1` and `T > 0`. -/
noncomputable def root (lam T : ℝ) : ℝ :=
  if h : -1 < lam ∧ lam < 1 ∧ 0 < T then (exists_unique_root h.1 h.2.1 h.2.2).exists.choose
  else 0

theorem root_spec {lam T : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hT : 0 < T) :
    -1 < root lam T ∧ tof lam (root lam T) = T := by
  unfold root
  split_ifs with h
  · exact (exists_unique_root h.1 h.2.1 h.2.2).exists.choose_spec
  · exact absurd ⟨hl0, hl1, hT⟩ h

/-- A point where `tof` exceeds `T` lies below the root, and one where it falls short lies above
it. -/
theorem root_between {lam T a b : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hT : 0 < T)
    (ha : -1 < a) (hb : -1 < b) (hta : T < tof lam a) (htb : tof lam b < T) :
    a < root lam T ∧ root lam T < b := by
  obtain ⟨hr, hrT⟩ := root_spec hl0 hl1 hT
  have hs := tof_strictAntiOn hl0 hl1
  constructor
  · by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · have := hs hr ha h; linarith
    · rw [h] at hrT; linarith
  · by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · have := hs hb hr h; linarith
    · rw [← h] at hrT; linarith

end Demos.Orbit.Lambert
