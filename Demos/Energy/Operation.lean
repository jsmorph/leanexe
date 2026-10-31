import Demos.Energy.Spec

/-! The gateway's operation over consecutive windows.  A run lists the accepted authorizations in
order of time: the snapshot of each and its accepted limits.  `OperatesIn` states, for one
accepted window from its snapshot to a time `t`, the device's response to the states that it
applies and the gateway's rules for snapshots and sends, with `state w` the state that the device
has applied at time `w`.  The device's response bounds battery power by its value at the
snapshot, where the device has settled, by 0, and by the intervals of the states that it applies
from the snapshot on, which covers transitions between states, protective trips and deratings
toward 0, and the return to fallback.  The gateway's rules record at each snapshot a state whose
interval holds battery power, and allow from one accepted snapshot to the next only the state
that it records, the command authorized from it, and fallback.  The program and its word layout
appear nowhere in this module. -/

namespace Demos.Energy.Spec

/-- The accepted authorizations of a gateway, in order of time: `length` of them, the `j`th with
its snapshot and its accepted limits. -/
structure Run where
  length : ℕ
  snapshot : ℕ → Snapshot
  limits : ℕ → Limits

namespace Run

/-- The time of the `j`th snapshot, s. -/
def time (r : Run) (j : ℕ) : ℝ := (r.snapshot j).time

/-- Time `w` lies from the `j`th snapshot to the next, or at or after the last. -/
def Between (r : Run) (j : ℕ) (w : ℝ) : Prop :=
  r.time j ≤ w ∧ (j + 1 < r.length → w < r.time (j + 1))

/-- Each accepted snapshot follows the one before, within the window length.  This is gateway
rule 5 together with the acceptance of a snapshot in each window. -/
def Spaced (r : Run) (p : Profile) : Prop :=
  ∀ j, j + 1 < r.length → r.time j < r.time (j + 1) ∧ r.time (j + 1) ≤ r.time j + p.window

end Run

namespace Trajectory

/-- The device's response and the gateway's rules for the `j`th accepted window, from its
snapshot to `t`, with `state w` the state that the device has applied at time `w`. -/
structure OperatesIn (x : Trajectory) (p : Profile) (r : Run) (state : ℝ → State) (j : ℕ)
    (t : ℝ) : Prop where
  /-- Gateway rule 1: at the snapshot, the device has settled, and battery power lies in the
  interval of the state that the snapshot records. -/
  settled : ((r.snapshot j).state.low p : ℝ) ≤ x.power (r.time j) ∧
    x.power (r.time j) ≤ (r.snapshot j).state.high p
  /-- Gateway rules 2 to 4 and assumption A7: from the snapshot to the next accepted snapshot,
  the state that the device has applied is the one that the snapshot records, the command
  authorized from that snapshot, or fallback. -/
  states : ∀ w ∈ Set.Icc (r.time j) t, r.Between j w →
    state w = (r.snapshot j).state ∨ state w = .command (r.limits j) ∨ state w = .fallback
  /-- The device's response, lower side: from the snapshot to each `v` up to `t`, battery power
  stays at or above every bound that holds for its value at the snapshot, for 0, and for the
  lower end of every state that the device applies from the snapshot to `v`. -/
  low : ∀ v ∈ Set.Icc (r.time j) t, ∀ m : ℝ, m ≤ x.power (r.time j) → m ≤ 0 →
    (∀ w ∈ Set.Icc (r.time j) v, m ≤ (state w).low p) → m ≤ x.power v
  /-- The device's response, upper side. -/
  high : ∀ v ∈ Set.Icc (r.time j) t, ∀ m : ℝ, x.power (r.time j) ≤ m → 0 ≤ m →
    (∀ w ∈ Set.Icc (r.time j) v, (state w).high p ≤ m) → x.power v ≤ m

end Trajectory

end Demos.Energy.Spec
