import Demos.Energy.Spec

/-! The integer conditions of the acceptance rule and the theorem that they bound every admitted
trajectory.  `Conditions p q s` states, in integers, the tests of each side on which the window's
power interval extends beyond the fallback interval: on the lower side the export cap and the
energy floor, and on the upper side the import cap and the energy ceiling.  The fallback interval
contains 0, so the lower end of the power interval is at most 0 and the upper end at least 0.  The
lower energy bound drains at the efficiency bound and the largest loss rate, rounded up, and the
upper bound gains at efficiency 1 with no loss.  `window_sound` states that the conditions give `WithinOrFallback` at
each time of the window for every trajectory admitted until that time. -/

namespace Demos.Energy.Spec

open Trajectory MeasureTheory

/-- The window's power interval extends below the fallback interval. -/
def lowerTested (p : Profile) (q : Snapshot) (s : ℤ) : Prop := powerLow p q s < p.fallbackLow

/-- The window's power interval extends above the fallback interval. -/
def upperTested (p : Profile) (q : Snapshot) (s : ℤ) : Prop := p.fallbackHigh < powerHigh p q s

/-- Energy that the lower bound drains over the window at power `b ≤ 0`, J, rounded up. -/
def drainLow (p : Profile) (b : ℤ) : ℤ :=
  (-b * p.window * 1000000 + p.eta - 1) / p.eta + p.lossMax * p.window

/-- The tests of the acceptance rule, in integers. -/
structure Conditions (p : Profile) (q : Snapshot) (s : ℤ) : Prop where
  exportCap : lowerTested p q s →
    (q.pvHigh : ℤ) ≤ q.loadLow + powerLow p q s + p.exportCap
  floor : lowerTested p q s → (p.floor : ℤ) ≤ q.energyLow ∧
    (p.floor : ℤ) + drainLow p (powerLow p q s) ≤ q.energyLow
  importCap : upperTested p q s →
    (q.loadHigh : ℤ) + powerHigh p q s ≤ p.importCap + q.pvLow
  ceiling : upperTested p q s → (q.energyHigh : ℤ) ≤ p.ceiling ∧
    (q.energyHigh : ℤ) + powerHigh p q s * p.window ≤ p.ceiling

theorem eff_pos {p : Profile} (h : 0 < p.eta) : 0 < p.eff := by
  unfold Profile.eff
  have : (0 : ℝ) < p.eta := by exact_mod_cast h
  positivity

theorem rateLow_mono {p : Profile} (he : 0 < p.eff) {a b : ℝ} (hab : a ≤ b) :
    rateLow p a ≤ rateLow p b := by
  unfold rateLow
  have key : (if 0 ≤ a then p.eff * a else a / p.eff) ≤ (if 0 ≤ b then p.eff * b else b / p.eff) := by
    split_ifs with ha hb hb
    · exact mul_le_mul_of_nonneg_left hab he.le
    · exact absurd (ha.trans hab) hb
    · have h1 : a / p.eff < 0 := div_neg_of_neg_of_pos (lt_of_not_ge ha) he
      have h2 : 0 ≤ p.eff * b := mul_nonneg he.le hb
      linarith
    · exact div_le_div_of_nonneg_right hab he.le
  linarith

/-- The rate of a trajectory is at least the lower rate at any power below the trajectory's. -/
theorem rate_ge {x : Trajectory} {p : Profile} {u B : ℝ} (he : 0 < p.eff)
    (hb : B ≤ x.power u) (hc : p.eff ≤ x.etaCharge u) (hd : p.eff ≤ x.etaDischarge u)
    (hl : x.loss u ≤ p.lossMax) : rateLow p B ≤ x.rate u := by
  refine (rateLow_mono he hb).trans ?_
  unfold rateLow Trajectory.rate
  by_cases h0 : 0 ≤ x.power u
  · simp only [h0, ↓reduceIte]
    rw [max_eq_left h0, max_eq_right (by linarith : -x.power u ≤ 0)]
    have : p.eff * x.power u ≤ x.etaCharge u * x.power u := mul_le_mul_of_nonneg_right hc h0
    simp only [zero_div, sub_zero]
    linarith
  · have h0' : x.power u < 0 := lt_of_not_ge h0
    simp only [h0, ↓reduceIte]
    rw [max_eq_right h0'.le, max_eq_left (by linarith : (0 : ℝ) ≤ -x.power u)]
    have hd0 : 0 < x.etaDischarge u := he.trans_le hd
    have hdiv : x.power u / p.eff ≤ x.power u / x.etaDischarge u := by
      rw [div_le_div_iff₀ he hd0]
      nlinarith
    have : -x.power u / x.etaDischarge u = -(x.power u / x.etaDischarge u) := by ring
    simp only [mul_zero, zero_sub]
    linarith

/-- The rate of a trajectory is at most its power. -/
theorem rate_le {x : Trajectory} {u : ℝ} (hc1 : x.etaCharge u ≤ 1)
    (hd0 : 0 < x.etaDischarge u) (hd1 : x.etaDischarge u ≤ 1) (hl : 0 ≤ x.loss u) :
    x.rate u ≤ x.power u := by
  unfold Trajectory.rate
  by_cases h0 : 0 ≤ x.power u
  · rw [max_eq_left h0, max_eq_right (by linarith : -x.power u ≤ 0)]
    have : x.etaCharge u * x.power u ≤ 1 * x.power u := mul_le_mul_of_nonneg_right hc1 h0
    simp only [zero_div, sub_zero]
    linarith
  · have h0' : x.power u < 0 := lt_of_not_ge h0
    rw [max_eq_right h0'.le, max_eq_left (by linarith : (0 : ℝ) ≤ -x.power u)]
    have : -x.power u ≤ -x.power u / x.etaDischarge u := by
      rw [le_div_iff₀ hd0]
      nlinarith
    simp only [mul_zero, zero_sub]
    linarith

/-- An affine function of `d` that meets a lower bound at `0` and at `w` meets it on `[0, w]`. -/
theorem affine_ge {e r f d w : ℝ} (h0 : f ≤ e) (hw : f ≤ e + r * w) (hd0 : 0 ≤ d) (hdw : d ≤ w) :
    f ≤ e + r * d := by
  by_cases hr : 0 ≤ r
  · nlinarith
  · nlinarith

/-- An affine function of `d` that meets an upper bound at `0` and at `w` meets it on `[0, w]`. -/
theorem affine_le {e r f d w : ℝ} (h0 : e ≤ f) (hw : e + r * w ≤ f) (hd0 : 0 ≤ d) (hdw : d ≤ w) :
    e + r * d ≤ f := by
  by_cases hr : 0 ≤ r
  · nlinarith
  · nlinarith

/-- Rounding up by `(n + d - 1) / d` gives at least `n / d`. -/
theorem ceil_div_ge {n d : ℤ} (hd : 0 < d) : (n : ℝ) / d ≤ (((n + d - 1) / d : ℤ) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Int.mul_ediv_add_emod (n + d - 1) d
  have h2 := Int.lt_iff_add_one_le.mp (Int.emod_lt_of_pos (n + d - 1) hd)
  have h3 : n ≤ d * ((n + d - 1) / d) := by linarith
  rw [div_le_iff₀ hdR]
  have : (n : ℝ) ≤ (d : ℝ) * (((n + d - 1) / d : ℤ) : ℝ) := by exact_mod_cast h3
  linarith

/-- The integer drain of the lower bound over the window at power `b ≤ 0` is at least the real
drain at the lower rate. -/
theorem drainLow_ge {p : Profile} (heta : 0 < p.eta) {b : ℤ} (hb : b ≤ 0) :
    rateLow p b * p.window ≥ -((drainLow p b : ℤ) : ℝ) := by
  have he := eff_pos heta
  have hbR : (b : ℝ) ≤ 0 := by exact_mod_cast hb
  have hrate : rateLow p b = (b : ℝ) / p.eff - p.lossMax := by
    unfold rateLow
    by_cases h0 : (0 : ℝ) ≤ b
    · have : (b : ℝ) = 0 := le_antisymm hbR h0
      simp [this]
    · simp [h0]
  have h := ceil_div_ge (n := -b * p.window * 1000000) (d := p.eta) (by exact_mod_cast heta)
  have hw : (0 : ℝ) ≤ p.window := by positivity
  unfold drainLow
  push_cast at h ⊢
  have : (-(b : ℝ)) * p.window * 1000000 / p.eta = -((b : ℝ) / p.eff) * p.window := by
    unfold Profile.eff; field_simp
  rw [this] at h
  rw [hrate]
  nlinarith

/-- A trajectory admitted until `t` has an interval-integrable rate on `[t_m, t]`. -/
theorem rate_integrable {x : Trajectory} {p : Profile} {q : Snapshot} {s : ℤ} {t : ℝ}
    (heta : 0 < p.eta) (ht : (q.time : ℝ) ≤ t) (hx : x.AdmittedUntil p q s t) :
    IntervalIntegrable x.rate volume (q.time : ℝ) t := by
  have he := eff_pos heta
  obtain ⟨hp, hc, hd, hl⟩ := hx.measurable
  have hm : AEMeasurable x.rate (volume.restrict (Set.Icc (q.time : ℝ) t)) := by
    unfold Trajectory.rate
    exact ((hc.mul (hp.max aemeasurable_const)).sub ((hp.neg.max aemeasurable_const).div hd)).sub hl
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
  refine IntegrableOn.of_bound (by simp [Real.volume_Icc]) hm.aestronglyMeasurable
    (max |rateLow p (powerLow p q s)| |(powerHigh p q s : ℝ)|) ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  obtain ⟨hpl, hph⟩ := hx.power u hu
  obtain ⟨hcl, hch, hdl, hdh⟩ := hx.efficiency u hu
  obtain ⟨hl0, hl1⟩ := hx.loss u hu
  have lo := rate_ge he hpl hcl hdl hl1
  have hi := (rate_le hch (he.trans_le hdl) hdh hl0).trans hph
  rw [Real.norm_eq_abs]
  exact abs_le_max_abs_abs lo hi

/-- Stored energy at `t` lies between the affine bounds at the ends of the power interval. -/
theorem energy_bounds {x : Trajectory} {p : Profile} {q : Snapshot} {s : ℤ} {t : ℝ}
    (heta : 0 < p.eta) (ht : (q.time : ℝ) ≤ t) (hx : x.AdmittedUntil p q s t) :
    (q.energyLow : ℝ) + rateLow p (powerLow p q s) * (t - q.time) ≤ x.energy t ∧
      x.energy t ≤ q.energyHigh + (powerHigh p q s : ℝ) * (t - q.time) := by
  have he := eff_pos heta
  have hI := rate_integrable heta ht hx
  have heq := hx.energy_eq t ⟨ht, le_refl t⟩
  obtain ⟨hE0, hE1⟩ := hx.energy_start
  have hlo : ∫ _ in (q.time : ℝ)..t, rateLow p (powerLow p q s) ≤ ∫ v in (q.time : ℝ)..t, x.rate v :=
    intervalIntegral.integral_mono_on ht intervalIntegrable_const hI fun u hu => by
      obtain ⟨hpl, _⟩ := hx.power u hu
      obtain ⟨hcl, _, hdl, _⟩ := hx.efficiency u hu
      exact rate_ge he hpl hcl hdl (hx.loss u hu).2
  have hhi : ∫ v in (q.time : ℝ)..t, x.rate v ≤ ∫ _ in (q.time : ℝ)..t, (powerHigh p q s : ℝ) :=
    intervalIntegral.integral_mono_on ht hI intervalIntegrable_const fun u hu => by
      obtain ⟨_, hph⟩ := hx.power u hu
      obtain ⟨hcl, hch, hdl, hdh⟩ := hx.efficiency u hu
      exact (rate_le hch (he.trans_le hdl) hdh (hx.loss u hu).1).trans hph
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  constructor <;> nlinarith

/-- Grid power at `t` lies between the bounds at the ends of the power interval. -/
theorem grid_bounds {x : Trajectory} {p : Profile} {q : Snapshot} {s : ℤ} {t : ℝ}
    (ht : (q.time : ℝ) ≤ t) (hx : x.AdmittedUntil p q s t) :
    (q.loadLow : ℝ) + powerLow p q s - q.pvHigh ≤ x.grid t ∧
      x.grid t ≤ (q.loadHigh : ℝ) + powerHigh p q s - q.pvLow := by
  have hu : t ∈ Set.Icc (q.time : ℝ) t := ⟨ht, le_refl t⟩
  obtain ⟨hpl, hph⟩ := hx.power t hu
  obtain ⟨hL0, hL1⟩ := hx.load t hu
  obtain ⟨hS0, hS1⟩ := hx.pv t hu
  unfold Trajectory.grid
  constructor <;> linarith

theorem powerLow_le (p : Profile) (q : Snapshot) (s : ℤ) : powerLow p q s ≤ p.fallbackLow :=
  min_le_right _ _

theorem le_powerHigh (p : Profile) (q : Snapshot) (s : ℤ) : p.fallbackHigh ≤ powerHigh p q s :=
  le_max_right _ _

/-- The conditions of the acceptance rule give the bounds of the acceptance rule at each time of
the window, for every trajectory admitted until that time. -/
theorem window_sound {p : Profile} {q : Snapshot} {s : ℤ} (heta : 0 < p.eta)
    (hF : p.fallbackLow ≤ 0 ∧ 0 ≤ p.fallbackHigh)
    (hc : Conditions p q s) {x : Trajectory} {t : ℝ} (ht : t ∈ window p q)
    (hx : x.AdmittedUntil p q s t) : x.WithinOrFallback p q t := by
  obtain ⟨ht0, ht1⟩ := ht
  have hd0 : (0 : ℝ) ≤ t - q.time := by linarith
  have hdw : t - q.time ≤ (p.window : ℝ) := by linarith
  obtain ⟨hElo, hEhi⟩ := energy_bounds heta ht0 hx
  obtain ⟨hGlo, hGhi⟩ := grid_bounds ht0 hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases hlt : lowerTested p q s
    · obtain ⟨hf0, hf1⟩ := hc.floor hlt
      have hterm := drainLow_ge heta ((powerLow_le p q s).trans hF.1)
      have h0 : (p.floor : ℝ) ≤ q.energyLow := by exact_mod_cast hf0
      have h1 : (p.floor : ℝ) ≤ q.energyLow + rateLow p (powerLow p q s) * p.window := by
        have : ((p.floor : ℤ) : ℝ) + (drainLow p (powerLow p q s) : ℝ) ≤
            ((q.energyLow : ℤ) : ℝ) := by exact_mod_cast hf1
        push_cast at this
        linarith
      exact (min_le_left _ _).trans ((affine_ge h0 h1 hd0 hdw).trans hElo)
    · have heq : powerLow p q s = p.fallbackLow :=
        le_antisymm (powerLow_le p q s) (not_lt.mp hlt)
      rw [heq] at hElo
      exact (min_le_right _ _).trans hElo
  · by_cases hut : upperTested p q s
    · obtain ⟨hc0, hc1⟩ := hc.ceiling hut
      have h0 : (q.energyHigh : ℝ) ≤ p.ceiling := by exact_mod_cast hc0
      have h1 : (q.energyHigh : ℝ) + (powerHigh p q s : ℝ) * p.window ≤ p.ceiling := by
        exact_mod_cast hc1
      exact hEhi.trans ((affine_le h0 h1 hd0 hdw).trans (le_max_left _ _))
    · have heq : powerHigh p q s = p.fallbackHigh :=
        le_antisymm (not_lt.mp hut) (le_powerHigh p q s)
      rw [heq] at hEhi
      exact hEhi.trans (le_max_right _ _)
  · by_cases hlt : lowerTested p q s
    · have h := hc.exportCap hlt
      have hR : (q.pvHigh : ℝ) ≤ q.loadLow + (powerLow p q s : ℝ) + p.exportCap := by
        exact_mod_cast h
      exact (min_le_left _ _).trans (by linarith)
    · have heq : powerLow p q s = p.fallbackLow :=
        le_antisymm (powerLow_le p q s) (not_lt.mp hlt)
      rw [heq] at hGlo
      exact (min_le_right _ _).trans hGlo
  · by_cases hut : upperTested p q s
    · have h := hc.importCap hut
      have hR : (q.loadHigh : ℝ) + (powerHigh p q s : ℝ) ≤ p.importCap + q.pvLow := by
        exact_mod_cast h
      exact (by linarith : x.grid t ≤ (p.importCap : ℝ)).trans (le_max_left _ _)
    · have heq : powerHigh p q s = p.fallbackHigh :=
        le_antisymm (not_lt.mp hut) (le_powerHigh p q s)
      rw [heq] at hGhi
      exact hGhi.trans (le_max_right _ _)

end Demos.Energy.Spec
