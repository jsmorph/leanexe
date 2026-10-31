import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The physical model and the claims of the energy authorizer, in integers and reals.  A profile
holds the site's limits and device parameters: energies in joules, powers in watts, times in
seconds, and the efficiency bound in parts per million.  A snapshot holds the measurement at time
`time`: the interval of stored energy, the state in force, and the intervals of load and PV output
for the window.  A trajectory gives stored energy, battery AC power (positive for charging), the
charge and discharge efficiencies, the auxiliary loss rate, the load, and the PV output as
functions of time.  A command sets power limits, within which the device's own control follows
the load, and a held setpoint `s` is the limits `[s, s]`.  `AdmittedUntil` states the assumptions
from the snapshot's time to a time `t` for proposed limits, `Within` the site's limits, and
`WithinOrFallback` the bounds of the acceptance rule: each site limit, or the worst case that an
immediate return to fallback admits.  The program and its word layout appear nowhere in this
module. -/

namespace Demos.Energy.Spec

/-- The site's limits and device parameters. -/
structure Profile where
  /-- Least permitted stored energy, J: the larger of the battery's minimum and the reserve. -/
  floor : ℕ
  /-- Greatest permitted stored energy, J. -/
  ceiling : ℕ
  /-- Largest upper limit of a command, W. -/
  chargeMax : ℕ
  /-- Largest magnitude of a command's lower limit, W. -/
  dischargeMax : ℕ
  /-- Largest grid import, W. -/
  importCap : ℕ
  /-- Largest grid export, W. -/
  exportCap : ℕ
  /-- Lower bound of the charge and discharge efficiencies, ppm. -/
  eta : ℕ
  /-- Largest auxiliary loss rate, W. -/
  lossMax : ℕ
  /-- Tolerance of battery power about a command's limits, W. -/
  tolerance : ℕ
  /-- Lower end of the fallback mode's power interval, W. -/
  fallbackLow : ℤ
  /-- Upper end of the fallback mode's power interval, W. -/
  fallbackHigh : ℤ
  /-- Transition time of a change of state, s. -/
  transition : ℕ
  /-- Window length, s. -/
  window : ℕ
  /-- The gateway's send deadline after a snapshot, s. -/
  sendDeadline : ℕ

/-- The power limits of a command, W: battery power stays between `low` and `high`, within the
tolerance.  A held setpoint `s` is the limits `[s, s]`. -/
structure Limits where
  low : ℤ
  high : ℤ

/-- The state of the device at a snapshot: a command with its limits, or the fallback mode. -/
inductive State where
  | command (limits : Limits)
  | fallback

/-- A measurement and the intervals that the window's assumptions use. -/
structure Snapshot where
  /-- Snapshot time `t_m`, s. -/
  time : ℕ
  /-- Interval of stored energy at `time`, J. -/
  energyLow : ℕ
  energyHigh : ℕ
  /-- State in force at `time`. -/
  state : State
  /-- Interval of instantaneous load over the window, W. -/
  loadLow : ℕ
  loadHigh : ℕ
  /-- Interval of instantaneous PV output over the window, W. -/
  pvLow : ℕ
  pvHigh : ℕ

/-- Lower end of the power interval of a state. -/
def State.low (p : Profile) : State → ℤ
  | .command c => c.low - p.tolerance
  | .fallback => p.fallbackLow

/-- Upper end of the power interval of a state. -/
def State.high (p : Profile) : State → ℤ
  | .command c => c.high + p.tolerance
  | .fallback => p.fallbackHigh

/-- Lower end of the window's power interval `B` for the proposed limits `c`: the least of the
state in force, the proposed limits widened by the tolerance, and the fallback interval. -/
def powerLow (p : Profile) (q : Snapshot) (c : Limits) : ℤ :=
  min (min (q.state.low p) (c.low - p.tolerance)) p.fallbackLow

/-- Upper end of the window's power interval `B` for the proposed limits `c`. -/
def powerHigh (p : Profile) (q : Snapshot) (c : Limits) : ℤ :=
  max (max (q.state.high p) (c.high + p.tolerance)) p.fallbackHigh

/-- The efficiency bound as a real number. -/
noncomputable def Profile.eff (p : Profile) : ℝ := (p.eta : ℝ) / 1000000

/-- The least rate of change of stored energy, W, while battery power is at least `b`: charging
at efficiency `eff`, or discharging at efficiency `eff`, less the largest loss rate.  It bounds the
rate from below only when `eff` is positive, which the profile's validity condition ensures. -/
noncomputable def rateLow (p : Profile) (b : ℝ) : ℝ :=
  (if 0 ≤ b then p.eff * b else b / p.eff) - p.lossMax

/-- Time, battery, and site quantities as functions of time in seconds. -/
structure Trajectory where
  /-- Usable stored energy, J. -/
  energy : ℝ → ℝ
  /-- Battery AC power, W, positive for charging. -/
  power : ℝ → ℝ
  /-- Charge efficiency. -/
  etaCharge : ℝ → ℝ
  /-- Discharge efficiency. -/
  etaDischarge : ℝ → ℝ
  /-- Auxiliary loss rate, W. -/
  loss : ℝ → ℝ
  /-- Site load, W. -/
  load : ℝ → ℝ
  /-- PV output, W. -/
  pv : ℝ → ℝ

namespace Trajectory

/-- Rate of change of stored energy, W: charging stores power times the charge efficiency,
discharging removes power divided by the discharge efficiency, and the auxiliary loss drains. -/
noncomputable def rate (x : Trajectory) (u : ℝ) : ℝ :=
  x.etaCharge u * max (x.power u) 0 - max (-x.power u) 0 / x.etaDischarge u - x.loss u

/-- Grid power, W, positive for import. -/
def grid (x : Trajectory) (u : ℝ) : ℝ := x.load u + x.power u - x.pv u

/-- The assumptions A1 and A3 to A5 from the snapshot's time to `t`: everything that a window's
theorem assumes except where battery power lies. -/
structure ModelUntil (x : Trajectory) (p : Profile) (q : Snapshot) (t : ℝ) : Prop where
  /-- A1: stored energy at the snapshot's time lies in the snapshot's interval. -/
  energy_start : (q.energyLow : ℝ) ≤ x.energy q.time ∧ x.energy q.time ≤ q.energyHigh
  /-- A3: efficiencies lie between the bound and 1. -/
  efficiency : ∀ u ∈ Set.Icc (q.time : ℝ) t,
    p.eff ≤ x.etaCharge u ∧ x.etaCharge u ≤ 1 ∧ p.eff ≤ x.etaDischarge u ∧ x.etaDischarge u ≤ 1
  /-- A3: the auxiliary loss rate lies between 0 and its largest value. -/
  loss : ∀ u ∈ Set.Icc (q.time : ℝ) t, 0 ≤ x.loss u ∧ x.loss u ≤ p.lossMax
  /-- A4: load lies in the snapshot's interval. -/
  load : ∀ u ∈ Set.Icc (q.time : ℝ) t, (q.loadLow : ℝ) ≤ x.load u ∧ x.load u ≤ q.loadHigh
  /-- A4: PV output lies in the snapshot's interval. -/
  pv : ∀ u ∈ Set.Icc (q.time : ℝ) t, (q.pvLow : ℝ) ≤ x.pv u ∧ x.pv u ≤ q.pvHigh
  /-- A5: power, efficiencies, and loss rate are measurable on `[time, t]`. -/
  measurable :
    AEMeasurable x.power (MeasureTheory.volume.restrict (Set.Icc (q.time : ℝ) t)) ∧
    AEMeasurable x.etaCharge (MeasureTheory.volume.restrict (Set.Icc (q.time : ℝ) t)) ∧
    AEMeasurable x.etaDischarge (MeasureTheory.volume.restrict (Set.Icc (q.time : ℝ) t)) ∧
    AEMeasurable x.loss (MeasureTheory.volume.restrict (Set.Icc (q.time : ℝ) t))
  /-- A5: stored energy is the energy at the snapshot's time plus the integral of the rate. -/
  energy_eq : ∀ u ∈ Set.Icc (q.time : ℝ) t,
    x.energy u = x.energy q.time + ∫ v in (q.time : ℝ)..u, x.rate v

/-- The assumptions A1 to A5 from the snapshot's time to `t`, for the proposed limits `c`. -/
structure AdmittedUntil (x : Trajectory) (p : Profile) (q : Snapshot) (c : Limits) (t : ℝ) :
    Prop extends ModelUntil x p q t where
  /-- A2: battery power lies in the window's power interval. -/
  power : ∀ u ∈ Set.Icc (q.time : ℝ) t,
    (powerLow p q c : ℝ) ≤ x.power u ∧ x.power u ≤ powerHigh p q c

/-- The site's limits at time `t`: stored energy between the floor and the ceiling, and grid power
between the export cap and the import cap. -/
def Within (x : Trajectory) (p : Profile) (t : ℝ) : Prop :=
  (p.floor : ℝ) ≤ x.energy t ∧ x.energy t ≤ p.ceiling ∧
    -(p.exportCap : ℝ) ≤ x.grid t ∧ x.grid t ≤ p.importCap

/-- The bounds of the acceptance rule at time `t`: each limit, or the model's worst case for an
immediate return to fallback at the snapshot's time, whichever is further out.  The fallback
worst cases are the energy bounds at the rates of the fallback interval, with efficiency 1 and no
loss for the upper bound, and the grid bounds at the ends of the fallback interval. -/
def WithinOrFallback (x : Trajectory) (p : Profile) (q : Snapshot) (t : ℝ) : Prop :=
  min (p.floor : ℝ) (q.energyLow + rateLow p p.fallbackLow * (t - q.time)) ≤ x.energy t ∧
    x.energy t ≤ max (p.ceiling : ℝ) (q.energyHigh + p.fallbackHigh * (t - q.time)) ∧
    min (-(p.exportCap : ℝ)) (q.loadLow + p.fallbackLow - q.pvHigh) ≤ x.grid t ∧
    x.grid t ≤ max (p.importCap : ℝ) (q.loadHigh + p.fallbackHigh - q.pvLow)

end Trajectory

/-- The window of a snapshot: from its time to its time plus the window length. -/
def window (p : Profile) (q : Snapshot) : Set ℝ := Set.Icc (q.time : ℝ) (q.time + p.window)

namespace Trajectory

variable {x : Trajectory} {p : Profile} {q : Snapshot} {t : ℝ}

/-- When the fallback worst case keeps the floor at `t`, the bounds give the floor. -/
theorem fallback_keeps_floor
    (hf : (p.floor : ℝ) ≤ q.energyLow + rateLow p p.fallbackLow * (t - q.time))
    (h : x.WithinOrFallback p q t) : (p.floor : ℝ) ≤ x.energy t := by
  have h1 := h.1
  rwa [min_eq_left hf] at h1

/-- When the fallback worst case keeps the ceiling at `t`, the bounds give the ceiling. -/
theorem fallback_keeps_ceiling
    (hf : (q.energyHigh : ℝ) + p.fallbackHigh * (t - q.time) ≤ p.ceiling)
    (h : x.WithinOrFallback p q t) : x.energy t ≤ p.ceiling := by
  have h2 := h.2.1
  rwa [max_eq_left hf] at h2

/-- When the fallback worst case keeps the export cap at `t`, the bounds give the export cap. -/
theorem fallback_keeps_export
    (hf : -(p.exportCap : ℝ) ≤ q.loadLow + p.fallbackLow - q.pvHigh)
    (h : x.WithinOrFallback p q t) : -(p.exportCap : ℝ) ≤ x.grid t := by
  have h3 := h.2.2.1
  rwa [min_eq_left hf] at h3

/-- When the fallback worst case keeps the import cap at `t`, the bounds give the import cap. -/
theorem fallback_keeps_import
    (hf : (q.loadHigh : ℝ) + p.fallbackHigh - q.pvLow ≤ p.importCap)
    (h : x.WithinOrFallback p q t) : x.grid t ≤ p.importCap := by
  have h4 := h.2.2.2
  rwa [max_eq_left hf] at h4

/-- When the fallback worst case keeps every site limit at `t`, the bounds give `Within`. -/
theorem within_of_fallback
    (hf : (p.floor : ℝ) ≤ q.energyLow + rateLow p p.fallbackLow * (t - q.time))
    (hc : (q.energyHigh : ℝ) + p.fallbackHigh * (t - q.time) ≤ p.ceiling)
    (he : -(p.exportCap : ℝ) ≤ q.loadLow + p.fallbackLow - q.pvHigh)
    (hi : (q.loadHigh : ℝ) + p.fallbackHigh - q.pvLow ≤ p.importCap)
    (h : x.WithinOrFallback p q t) : x.Within p t :=
  ⟨fallback_keeps_floor hf h, fallback_keeps_ceiling hc h, fallback_keeps_export he h,
    fallback_keeps_import hi h⟩

end Trajectory

end Demos.Energy.Spec
