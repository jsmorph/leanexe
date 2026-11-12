import Demos.PassiveSafety.Model

/-!
The trajectory of a scenario between its burns, and Taylor's theorem of order two.  `smooth` is
the closed form from the initial state plus the closed forms of the burns that a scenario executes
at or before a time `S`.  On an interval of time with no burn time of the scenario in its
interior, `Soundness.lean` equates its position with that of `path`.  `smooth_motion` states its
derivatives: the velocity of the same terms for the position, and the acceleration of the
equations for the velocity.  `taylor_two` is Taylor's theorem with the Lagrange remainder, and
`sep_derivs` and `rc_derivs` give the first and second derivatives of the squared distances of
every `Motion`.
-/

namespace Demos.PassiveSafety.Model

open Real

/-! ### Rolle's theorem, the mean value theorem, and Taylor's theorem -/

/-- Rolle's theorem for two points in either order. -/
theorem rolle_between {φ φ' : ℝ → ℝ} (hd : ∀ x, HasDerivAt φ (φ' x) x) {u w : ℝ} (hne : u ≠ w)
    (h : φ u = φ w) : ∃ c, min u w < c ∧ c < max u w ∧ φ' c = 0 := by
  have hc : ∀ a b, ContinuousOn φ (Set.Icc a b) :=
    fun _ _ x _ => (hd x).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with h1 | h1
  · obtain ⟨c, ⟨c1, c2⟩, hc0⟩ := exists_hasDerivAt_eq_zero h1 (hc u w) h fun x _ => hd x
    exact ⟨c, by rw [min_eq_left h1.le]; exact c1, by rw [max_eq_right h1.le]; exact c2, hc0⟩
  · obtain ⟨c, ⟨c1, c2⟩, hc0⟩ := exists_hasDerivAt_eq_zero h1 (hc w u) h.symm fun x _ => hd x
    exact ⟨c, by rw [min_eq_right h1.le]; exact c1, by rw [max_eq_left h1.le]; exact c2, hc0⟩

/-- The mean value theorem for a function with a derivative everywhere. -/
theorem mean_value {f f1 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x) (m t : ℝ) :
    ∃ η, min m t ≤ η ∧ η ≤ max m t ∧ f t = f m + f1 η * (t - m) := by
  by_cases hmt : m = t
  · subst hmt
    exact ⟨m, min_le_left _ _, le_max_left _ _, by ring⟩
  have hd : t - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmt)
  set K := (f t - f m) / (t - m) with hK
  have e : K * (t - m) = f t - f m := by rw [hK]; field_simp
  have hφ : ∀ x, HasDerivAt (fun x => f x - f m - K * (x - m)) (f1 x - K) x := fun x =>
    (((h1 x).sub_const (f m)).sub (((hasDerivAt_id' x).sub_const m).const_mul K)).congr_deriv
      (by ring)
  obtain ⟨η, h1', h2', h0⟩ := rolle_between hφ hmt (by
    show f m - f m - K * (m - m) = f t - f m - K * (t - m)
    rw [e]; ring)
  refine ⟨η, h1'.le, h2'.le, ?_⟩
  have hη : f1 η = K := by linarith
  rw [hη, e]; ring

/-- Taylor's theorem of order two with the Lagrange remainder, for a function with two
derivatives everywhere. -/
theorem taylor_two {f f1 f2 : ℝ → ℝ} (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) (m t : ℝ) :
    ∃ ξ, min m t ≤ ξ ∧ ξ ≤ max m t ∧
      f t = f m + f1 m * (t - m) + f2 ξ * ((t - m) * (t - m)) / 2 := by
  by_cases hmt : m = t
  · subst hmt
    exact ⟨m, min_le_left _ _, le_max_left _ _, by ring⟩
  have hd : (t - m) * (t - m) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hmt)) (sub_ne_zero.mpr (Ne.symm hmt))
  set K := 2 * (f t - f m - f1 m * (t - m)) / ((t - m) * (t - m)) with hK
  have e : K * ((t - m) * (t - m)) / 2 = f t - f m - f1 m * (t - m) := by rw [hK]; field_simp
  have hφ : ∀ x, HasDerivAt
      (fun x => f x - f m - f1 m * (x - m) - K * ((x - m) * (x - m)) / 2)
      (f1 x - f1 m - K * (x - m)) x := fun x => by
    have hx := (hasDerivAt_id' x).sub_const m
    exact ((((h1 x).sub_const (f m)).sub (hx.const_mul (f1 m))).sub
      ((hx.mul hx).const_mul K |>.div_const 2)).congr_deriv (by ring)
  obtain ⟨c, c1, c2, hc0⟩ := rolle_between hφ hmt (by
    show f m - f m - f1 m * (m - m) - K * ((m - m) * (m - m)) / 2 =
      f t - f m - f1 m * (t - m) - K * ((t - m) * (t - m)) / 2
    rw [e]; ring)
  have hψ : ∀ x, HasDerivAt (fun x => f1 x - f1 m - K * (x - m)) (f2 x - K) x := fun x =>
    (((h2 x).sub_const (f1 m)).sub (((hasDerivAt_id' x).sub_const m).const_mul K)).congr_deriv
      (by ring)
  have hcm : m ≠ c := by
    intro h
    rw [← h] at c1 c2
    rcases le_total m t with h | h
    · rw [min_eq_left h] at c1; exact lt_irrefl m c1
    · rw [max_eq_left h] at c2; exact lt_irrefl m c2
  obtain ⟨ξ, ξ1, ξ2, hξ0⟩ := rolle_between hψ hcm (by
    show f1 m - f1 m - K * (m - m) = f1 c - f1 m - K * (c - m)
    rw [hc0]; ring)
  refine ⟨ξ, (le_min (min_le_left _ _) c1.le).trans ξ1.le,
    ξ2.le.trans (max_le (le_max_left _ _) c2.le), ?_⟩
  have hξ : f2 ξ = K := by linarith
  rw [hξ, e]; ring

/-! ### The trajectory between burns -/

/-- The term of burn `i` of a plan in scenario `j` between burns: the closed form of the burn's
velocity change from its time when the scenario executes the burn at or before `S`, and zero
otherwise. -/
noncomputable def early (n S : ℝ) (N j : ℕ) (bs : List Burn) (i : ℕ) (τ : ℝ) : State :=
  if runs N j i = true ∧ (bs.getD i Burn.none).t ≤ S then
    flow n (τ - (bs.getD i Burn.none).t) (bs.getD i Burn.none).kick
  else 0

/-- Component `c` of the closed form from `s` plus the terms of `early` of the burns of `bs`. -/
noncomputable def smooth (c : State → ℝ) (n S : ℝ) (s : State) (N j : ℕ) (bs : List Burn)
    (τ : ℝ) : ℝ :=
  c (flow n τ s) + ∑ i ∈ Finset.range bs.length, c (early n S N j bs i τ)

theorem solves_shift {n : ℝ} (hn : n ≠ 0) (u : State) (t0 τ : ℝ) :
    Solves n (fun τ => flow n (τ - t0) u) τ := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := flow_hasDerivAt hn u (τ - t0)
  exact ⟨h0.comp_sub_const τ t0, h1.comp_sub_const τ t0, h2.comp_sub_const τ t0,
    h3.comp_sub_const τ t0, h4.comp_sub_const τ t0, h5.comp_sub_const τ t0⟩

theorem solves_zero (n τ : ℝ) : Solves n (fun _ => (0 : State)) τ := by
  have h := hasDerivAt_const τ (0 : ℝ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simpa [field] using h

theorem early_solves {n : ℝ} (hn : n ≠ 0) (S : ℝ) (N j : ℕ) (bs : List Burn) (i : ℕ) (τ : ℝ) :
    Solves n (early n S N j bs i) τ := by
  by_cases h : runs N j i = true ∧ (bs.getD i Burn.none).t ≤ S
  · have e : early n S N j bs i =
        fun τ => flow n (τ - (bs.getD i Burn.none).t) (bs.getD i Burn.none).kick :=
      funext fun _ => ite_eq_left h
    rw [e]
    exact solves_shift hn _ _ τ
  · have e : early n S N j bs i = fun _ => 0 := funext fun _ => ite_eq_right h
    rw [e]
    exact solves_zero n τ

/-- The functions `x`, `y`, `z`, `vx`, `vy`, and `vz` of time satisfy the equations at every
time: the velocity is the derivative of the position, and the acceleration of the equations the
derivative of the velocity. -/
def Motion (n : ℝ) (x y z vx vy vz : ℝ → ℝ) : Prop :=
  ∀ τ, HasDerivAt x (vx τ) τ ∧ HasDerivAt y (vy τ) τ ∧ HasDerivAt z (vz τ) τ ∧
    HasDerivAt vx (3 * n ^ 2 * x τ + 2 * n * vy τ) τ ∧ HasDerivAt vy (-(2 * n * vx τ)) τ ∧
    HasDerivAt vz (-(n ^ 2 * z τ)) τ

/-- The trajectory between burns satisfies the equations. -/
theorem smooth_motion {n : ℝ} (hn : n ≠ 0) (S : ℝ) (s : State) (N j : ℕ) (bs : List Burn) :
    Motion n (smooth State.x n S s N j bs) (smooth State.y n S s N j bs)
      (smooth State.z n S s N j bs) (smooth State.vx n S s N j bs)
      (smooth State.vy n S s N j bs) (smooth State.vz n S s N j bs) := by
  intro τ
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := flow_hasDerivAt hn s τ
  have e := fun i (_ : i ∈ Finset.range bs.length) => early_solves hn S N j bs i τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact a0.add (HasDerivAt.fun_sum fun i hi => (e i hi).1)
  · exact a1.add (HasDerivAt.fun_sum fun i hi => (e i hi).2.1)
  · exact a2.add (HasDerivAt.fun_sum fun i hi => (e i hi).2.2.1)
  · refine (a3.add (HasDerivAt.fun_sum fun i hi => (e i hi).2.2.2.1)).congr_deriv ?_
    simp only [field, smooth, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  · refine (a4.add (HasDerivAt.fun_sum fun i hi => (e i hi).2.2.2.2.1)).congr_deriv ?_
    simp only [field, smooth, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  · refine (a5.add (HasDerivAt.fun_sum fun i hi => (e i hi).2.2.2.2.2)).congr_deriv ?_
    simp only [field, smooth, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring

/-- The squared separation of a motion, its derivative, and its second derivative, in the
grouping of `sepTaylor`. -/
theorem sep_derivs {n : ℝ} {x y z vx vy vz : ℝ → ℝ} (h : Motion n x y z vx vy vz) :
    (∀ τ, HasDerivAt (fun τ => x τ ^ 2 + y τ ^ 2 + z τ ^ 2)
      (2 * (x τ * vx τ + y τ * vy τ + z τ * vz τ)) τ) ∧
    (∀ τ, HasDerivAt (fun τ => 2 * (x τ * vx τ + y τ * vy τ + z τ * vz τ))
      (2 * ((vx τ ^ 2 + vy τ ^ 2 + vz τ ^ 2) +
        (x τ * (3 * (n * n) * x τ + 2 * n * vy τ) + y τ * -(2 * n * vx τ) +
          z τ * -(n * n * z τ)))) τ) := by
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨hx, hy, hz, -, -, -⟩ := h τ
    have ef : (fun τ => x τ ^ 2 + y τ ^ 2 + z τ ^ 2) =
        fun τ => x τ * x τ + y τ * y τ + z τ * z τ := by
      funext τ; ring
    rw [ef]
    exact (((hx.mul hx).add (hy.mul hy)).add (hz.mul hz)).congr_deriv (by ring)
  · obtain ⟨hx, hy, hz, hvx, hvy, hvz⟩ := h τ
    exact ((((hx.mul hvx).add (hy.mul hvy)).add (hz.mul hvz)).const_mul 2).congr_deriv
      (by ring)

/-- The squared radial and cross-track distance of a motion, its derivative, and its second
derivative, in the grouping of `rcTaylor`. -/
theorem rc_derivs {n : ℝ} {x y z vx vy vz : ℝ → ℝ} (h : Motion n x y z vx vy vz) :
    (∀ τ, HasDerivAt (fun τ => x τ ^ 2 + z τ ^ 2) (2 * (x τ * vx τ + z τ * vz τ)) τ) ∧
    (∀ τ, HasDerivAt (fun τ => 2 * (x τ * vx τ + z τ * vz τ))
      (2 * ((vx τ ^ 2 + vz τ ^ 2) +
        (x τ * (3 * (n * n) * x τ + 2 * n * vy τ) + z τ * -(n * n * z τ)))) τ) := by
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨hx, -, hz, -, -, -⟩ := h τ
    have ef : (fun τ => x τ ^ 2 + z τ ^ 2) = fun τ => x τ * x τ + z τ * z τ := by
      funext τ; ring
    rw [ef]
    exact ((hx.mul hx).add (hz.mul hz)).congr_deriv (by ring)
  · obtain ⟨hx, -, hz, hvx, -, hvz⟩ := h τ
    exact (((hx.mul hvx).add (hz.mul hvz)).const_mul 2).congr_deriv (by ring)

end Demos.PassiveSafety.Model
