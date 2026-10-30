import Demos.Energy.Authorize
import Demos.Energy.Verified
import Verified.Call

/-! The energy authorizer under the test site's profile table, and its module.  `site_valid`
proves that the table meets the profile's validity condition.  `authorize_sound` states that an
accepted setpoint gives the bounds of the acceptance rule at each time of the window for every
trajectory admitted until that time, and `authorize_accepted` the setpoint and the expiry of an
accepted result.  `energy_authorize` states that the module's bytes decode to the module, whose
export `authorize` is function 17, whose start store is ready, and whose entry returns, without a
trap and from every ready store, the authorizer's decision, which has those properties. -/

namespace Demos.Energy.Theorems

open Spec Words Authorize
open _root_.Demos.Energy.Verified

theorem site_valid : ProfileValid site := by
  constructor <;> decide +kernel

/-- An accepted setpoint gives the bounds of the acceptance rule at each time of the window for
every trajectory admitted until that time. -/
theorem authorize_sound {xs : Array UInt64} (h : (authorize xs).status = .accepted)
    {x : Trajectory} {t : ℝ} (ht : t ∈ window (profileOf site) (snapshotOf xs))
    (hx : x.AdmittedUntil (profileOf site) (snapshotOf xs) (setpointOf xs) t) :
    x.WithinOrFallback (profileOf site) (snapshotOf xs) t :=
  authorizeWith_sound site_valid h ht hx

/-- An accepted result holds the proposed setpoint and the expiry `t_m + W - τ`. -/
theorem authorize_accepted {xs : Array UInt64} (h : (authorize xs).status = .accepted) :
    (authorize xs).setpoint = xs[10]! ∧
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
store is ready, and whose entry computes the authorizer, whose accepted setpoints give the bounds
of the acceptance rule. -/
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
          x.AdmittedUntil (profileOf site) (snapshotOf xs) (setpointOf xs) t →
          x.WithinOrFallback (profileOf site) (snapshotOf xs) t := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, energy_export,
    _root_.Verified.Ready.initial rfl compiled.initial,
    authorize_call, fun _ h _ _ ht hx => authorize_sound h ht hx⟩

end Demos.Energy.Theorems
