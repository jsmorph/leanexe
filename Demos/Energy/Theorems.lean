import Demos.Energy.Authorize
import Demos.Energy.Verified
import Verified.Call

/-! The energy authorizer under the test site's profile table, and its module.  `site_valid`
proves that the table meets the profile's validity condition.  `authorize_sound` states that
accepted limits give the bounds of the acceptance rule at each time of the window for every
trajectory admitted until that time, `authorize_admits` that some trajectory is admitted,
`authorize_operation` that consecutive accepted windows cover the gateway's operation, and
`authorize_accepted` the limits and the expiry of an accepted result.  `energy_authorize` states
that the module's bytes decode to the module, whose export `authorize` is function 17, whose
start store is ready, and whose entry returns, without a trap and from every ready store, the
authorizer's decision, which has those properties. -/

namespace Demos.Energy.Theorems

open Spec Words Authorize
open _root_.Demos.Energy.Verified

theorem site_valid : ProfileValid site := by
  constructor <;> decide +kernel

/-- Accepted limits give the bounds of the acceptance rule at each time of the window for every
trajectory admitted until that time. -/
theorem authorize_sound {xs : Array UInt64} (h : (authorize xs).status = .accepted)
    {x : Trajectory} {t : ℝ} (ht : t ∈ window (profileOf site) (snapshotOf xs))
    (hx : x.AdmittedUntil (profileOf site) (snapshotOf xs) (limitsOf xs) t) :
    x.WithinOrFallback (profileOf site) (snapshotOf xs) t :=
  authorizeWith_sound site_valid h ht hx

/-- For accepted limits, some trajectory is admitted until every time. -/
theorem authorize_admits {xs : Array UInt64} (h : (authorize xs).status = .accepted) (t : ℝ) :
    ∃ x : Trajectory, x.AdmittedUntil (profileOf site) (snapshotOf xs) (limitsOf xs) t :=
  authorizeWith_admits site_valid h t

/-- Consecutive inputs that `authorize` accepted, sent under the gateway's rules, give at every
time from the first snapshot to the end of the last window the bounds of an accepted window that
contains that time, for a trajectory that meets that window's other assumptions until then. -/
theorem authorize_operation {n : ℕ} {ys : ℕ → Array UInt64}
    (h : ∀ j < n, (authorize (ys j)).status = .accepted)
    (hr : (runOf n ys).Spaced (profileOf site)) (h0 : 0 < n) {x : Trajectory}
    {state : ℝ → State} {t : ℝ} (ht0 : (runOf n ys).time 0 ≤ t)
    (ht1 : t ≤ (runOf n ys).time (n - 1) + (profileOf site).window) :
    ∃ j < n, t ∈ window (profileOf site) (snapshotOf (ys j)) ∧
      (x.ModelUntil (profileOf site) (snapshotOf (ys j)) t →
        x.OperatesIn (profileOf site) (runOf n ys) state j t →
        x.WithinOrFallback (profileOf site) (snapshotOf (ys j)) t) :=
  authorizeWith_operation site_valid h hr h0 ht0 ht1

/-- An accepted result holds the proposed limits and the expiry `t_m + W - τ`. -/
theorem authorize_accepted {xs : Array UInt64} (h : (authorize xs).status = .accepted) :
    (authorize xs).low = xs[11]! ∧ (authorize xs).high = xs[12]! ∧
      (authorize xs).expiry.toNat =
        (snapshotOf xs).time + (profileOf site).window - (profileOf site).transition :=
  authorizeWith_accepted site_valid h

theorem energy_export :
    ({ name := "authorize", funcIdx := 17 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 17 returns, without a trap and from every ready store, the authorizer's decision. -/
theorem authorize_call :
    _root_.Verified.Call compiled.module compiled.tables 17 authorize (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.authorize.implements compiled.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩)

/-- The module's bytes decode to the module, whose export `authorize` is function 17, whose start
store is ready, and whose entry computes the authorizer, whose accepted limits give the bounds of
the acceptance rule. -/
theorem energy_authorize :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "authorize", funcIdx := 17 } : Wasm.Export) ∈ compiled.module.exports ∧
      _root_.Verified.Ready compiled.module compiled.tables
        (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      _root_.Verified.Call compiled.module compiled.tables 17 authorize (fun _ _ _ => True)
        (fun _ _ _ _ _ => True) ∧
      ∀ xs : Array UInt64, (authorize xs).status = .accepted →
        ∀ (x : Trajectory) (t : ℝ), t ∈ window (profileOf site) (snapshotOf xs) →
          x.AdmittedUntil (profileOf site) (snapshotOf xs) (limitsOf xs) t →
          x.WithinOrFallback (profileOf site) (snapshotOf xs) t := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, energy_export,
    _root_.Verified.Ready.initial rfl compiled.initial,
    authorize_call, fun _ h _ _ ht hx => authorize_sound h ht hx⟩

end Demos.Energy.Theorems
