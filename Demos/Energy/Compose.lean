import Demos.Energy.Operation
import Demos.Energy.Window

/-! Consecutive windows.  `power_in_window` derives assumption A2 of an accepted window from the
device's response and the gateway's rules, from the window's snapshot to the next.  `run_sound`
gives the window's bounds at each time from its snapshot to the next, `run_covered` that every
time from the first snapshot to the end of the last window lies in the window of the latest
accepted snapshot at or before it, and `operation_sound` combines them.  `operates_exists` shows
that the premises can hold together. -/

namespace Demos.Energy.Spec

open Trajectory

variable {p : Profile} {r : Run} {x : Trajectory} {state : ℝ → State} {t : ℝ} {j : ℕ}

theorem powerLow_le_state (p : Profile) (q : Snapshot) (c : Limits) :
    powerLow p q c ≤ q.state.low p :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem powerLow_le_command (p : Profile) (q : Snapshot) (c : Limits) :
    powerLow p q c ≤ c.low - p.tolerance :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem state_le_powerHigh (p : Profile) (q : Snapshot) (c : Limits) :
    q.state.high p ≤ powerHigh p q c :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem command_le_powerHigh (p : Profile) (q : Snapshot) (c : Limits) :
    c.high + p.tolerance ≤ powerHigh p q c :=
  (le_max_right _ _).trans (le_max_left _ _)

/-- The device's response and the gateway's rules keep battery power in an accepted window's
power interval from its snapshot until `t`, before the next snapshot. -/
theorem power_in_window (hF : p.fallbackLow ≤ 0 ∧ 0 ≤ p.fallbackHigh)
    (ho : x.OperatesIn p r state j t) (hb : r.Between j t) :
    ∀ u ∈ Set.Icc (r.time j) t,
      (powerLow p (r.snapshot j) (r.limits j) : ℝ) ≤ x.power u ∧
        x.power u ≤ powerHigh p (r.snapshot j) (r.limits j) := by
  intro u hu
  have hs := ho.settled
  have hstate : ∀ w ∈ Set.Icc (r.time j) u, state w = (r.snapshot j).state ∨
      state w = .command (r.limits j) ∨ state w = .fallback := fun w hw =>
    ho.states w ⟨hw.1, hw.2.trans hu.2⟩
      ⟨hw.1, fun hn => lt_of_le_of_lt (hw.2.trans hu.2) (hb.2 hn)⟩
  constructor
  · refine ho.low u hu _ ?_ ?_ ?_
    · exact le_trans (by exact_mod_cast powerLow_le_state p _ _) hs.1
    · exact_mod_cast (powerLow_le p _ _).trans hF.1
    · intro w hw
      rcases hstate w hw with h | h | h
      · rw [h]
        exact_mod_cast powerLow_le_state p _ _
      · rw [h]
        exact_mod_cast powerLow_le_command p _ _
      · rw [h]
        exact_mod_cast powerLow_le p _ _
  · refine ho.high u hu _ ?_ ?_ ?_
    · exact le_trans hs.2 (by exact_mod_cast state_le_powerHigh p _ _)
    · exact_mod_cast hF.2.trans (le_powerHigh p _ _)
    · intro w hw
      rcases hstate w hw with h | h | h
      · rw [h]
        exact_mod_cast state_le_powerHigh p _ _
      · rw [h]
        exact_mod_cast command_le_powerHigh p _ _
      · rw [h]
        exact_mod_cast le_powerHigh p _ _

/-- An accepted window's bounds hold at each time of the window from its snapshot to the next,
for a trajectory that meets the window's other assumptions until that time and under the device's
response and the gateway's rules. -/
theorem run_sound (heta : 0 < p.eta) (hF : p.fallbackLow ≤ 0 ∧ 0 ≤ p.fallbackHigh)
    (hc : Conditions p (r.snapshot j) (r.limits j)) (hb : r.Between j t)
    (ht : t ∈ window p (r.snapshot j)) (hm : x.ModelUntil p (r.snapshot j) t)
    (ho : x.OperatesIn p r state j t) :
    x.WithinOrFallback p (r.snapshot j) t :=
  window_sound heta hF hc ht { hm with power := power_in_window hF ho hb }

/-- When accepted snapshots lie at most a window apart, every time from the first snapshot to the
end of the last window lies in the window of the latest accepted snapshot at or before it. -/
theorem run_covered (hr : r.Spaced p) (h0 : 0 < r.length) (ht0 : r.time 0 ≤ t)
    (ht1 : t ≤ r.time (r.length - 1) + p.window) :
    ∃ j < r.length, r.Between j t ∧ t ∈ window p (r.snapshot j) := by
  classical
  set j := Nat.findGreatest (fun j => r.time j ≤ t) (r.length - 1) with hjdef
  have hjn : j ≤ r.length - 1 := Nat.findGreatest_le _
  have hjt : r.time j ≤ t := Nat.findGreatest_spec (P := fun j => r.time j ≤ t)
    (Nat.zero_le _) ht0
  have hnext : j + 1 < r.length → t < r.time (j + 1) := by
    intro hn
    by_contra hle
    exact Nat.findGreatest_is_greatest (P := fun j => r.time j ≤ t) (Nat.lt_succ_self j)
      (by omega) (not_lt.mp hle)
  refine ⟨j, by omega, ⟨hjt, hnext⟩, hjt, ?_⟩
  by_cases hn : j + 1 < r.length
  · exact (hnext hn).le.trans (hr j hn).2
  · have hlast : j = r.length - 1 := by omega
    rw [hlast]
    exact ht1

/-- When accepted snapshots lie at most a window apart, every time from the first snapshot to the
end of the last window lies in the window of the latest accepted snapshot at or before it, whose
bounds hold at that time for a trajectory that meets that window's other assumptions, the
device's response, and the gateway's rules until that time. -/
theorem operation_sound (heta : 0 < p.eta) (hF : p.fallbackLow ≤ 0 ∧ 0 ≤ p.fallbackHigh)
    (hc : ∀ j < r.length, Conditions p (r.snapshot j) (r.limits j)) (hr : r.Spaced p)
    (h0 : 0 < r.length) (ht0 : r.time 0 ≤ t) (ht1 : t ≤ r.time (r.length - 1) + p.window) :
    ∃ j < r.length, r.Between j t ∧ t ∈ window p (r.snapshot j) ∧
      (x.ModelUntil p (r.snapshot j) t → x.OperatesIn p r state j t →
        x.WithinOrFallback p (r.snapshot j) t) := by
  obtain ⟨j, hj, hb, hw⟩ := run_covered hr h0 ht0 ht1
  exact ⟨j, hj, hb, hw, fun hm ho => run_sound heta hF (hc j hj) hb hw hm ho⟩

/-- For a window with ordered intervals and a nonempty interval of the state in force, some
trajectory and states applied meet the window's other assumptions, the device's response, and the
gateway's rules until every time, so `run_sound` and `operation_sound` are not vacuous.  The
witness holds battery power at the lower end of the state in force, both efficiencies at 1, and
the loss at 0, with stored energy starting at the lower end of its interval and changing at the
battery's rate, and load and PV at the lower ends of their intervals. -/
theorem operates_exists (r : Run) (j : ℕ) (t : ℝ) (heta : p.eta ≤ 1000000)
    (hE : (r.snapshot j).energyLow ≤ (r.snapshot j).energyHigh)
    (hL : (r.snapshot j).loadLow ≤ (r.snapshot j).loadHigh)
    (hS : (r.snapshot j).pvLow ≤ (r.snapshot j).pvHigh)
    (hP : (r.snapshot j).state.low p ≤ (r.snapshot j).state.high p) :
    ∃ (x : Trajectory) (state : ℝ → State),
      x.ModelUntil p (r.snapshot j) t ∧ x.OperatesIn p r state j t := by
  set q := r.snapshot j with hq
  set c0 : ℝ := (q.state.low p : ℝ) with hc0
  have heff := eff_le_one heta
  have hm : max c0 0 - max (-c0) 0 = c0 := by
    rcases le_total 0 c0 with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
  refine ⟨⟨fun u => q.energyLow + c0 * (u - q.time), fun _ => c0, fun _ => 1, fun _ => 1,
    fun _ => 0, fun _ => q.loadLow, fun _ => q.pvLow⟩, fun _ => q.state,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · show (q.energyLow : ℝ) ≤ q.energyLow + c0 * ((q.time : ℝ) - q.time) ∧
      (q.energyLow : ℝ) + c0 * ((q.time : ℝ) - q.time) ≤ q.energyHigh
    rw [sub_self, mul_zero, add_zero]
    exact ⟨le_refl _, by exact_mod_cast hE⟩
  · intro u _
    exact ⟨heff, le_refl _, heff, le_refl _⟩
  · intro u _
    exact ⟨le_refl _, by positivity⟩
  · intro u _
    show (q.loadLow : ℝ) ≤ q.loadLow ∧ (q.loadLow : ℝ) ≤ q.loadHigh
    exact ⟨le_refl _, by exact_mod_cast hL⟩
  · intro u _
    show (q.pvLow : ℝ) ≤ q.pvLow ∧ (q.pvLow : ℝ) ≤ q.pvHigh
    exact ⟨le_refl _, by exact_mod_cast hS⟩
  · exact ⟨aemeasurable_const, aemeasurable_const, aemeasurable_const, aemeasurable_const⟩
  · intro u _
    show (q.energyLow : ℝ) + c0 * (u - q.time) =
      (q.energyLow : ℝ) + c0 * ((q.time : ℝ) - q.time) +
        ∫ v in (q.time : ℝ)..u, (1 : ℝ) * max c0 0 - max (-c0) 0 / 1 - 0
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    linear_combination ((q.time : ℝ) - u) * hm
  · show c0 ≤ c0 ∧ c0 ≤ (q.state.high p : ℝ)
    refine ⟨le_refl _, ?_⟩
    rw [hc0]
    exact_mod_cast hP
  · intro w _ _
    exact Or.inl rfl
  · intro v _ m hm _ _
    exact hm
  · intro v _ m hm _ _
    exact hm

end Demos.Energy.Spec
