import Demos.Gate.GateVerified
import Demos.Gate.GateSoundness
import Verified.Call

/-! The call of the module's export `gate`.  The program allocates the arrays of its elimination,
so the call returns without a trap from a ready store in which the allocator's `top` can rise by
the generated bound `gateCompiled.gate.bound`, and `top` rises by at most that much.
`gate_module` joins the module's bytes, the export, the readiness of the start store, the call,
and the conclusions of `gate_sound` for accepted results. -/

namespace Demos.Gate

open CodeLib.IEEE64 (value Finite)

theorem gate_export :
    ({ name := "gate", funcIdx := 30 } : Wasm.Export) ∈ gateCompiled.module.exports := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The export `gate` returns `gate nu s g` without a trap from every ready store with room for
`gateCompiled.gate.bound (nu, s, g)` bytes. -/
theorem gate_callSpec :
    _root_.Verified.CallSpec gateCompiled.module gateCompiled.tables 30
      (fun x : Array Float × Array Float × Float => gate x.1 x.2.1 x.2.2)
      gateCompiled.gate.bound :=
  _root_.Verified.ImplementsTables.call (_root_.Verified.ImplementsTables.ofA
    gateCompiled.gate.trapFree) gateCompiled.tables nofun

/-- The module's bytes decode to the module, whose export `gate` returns `gate nu s g` without a
trap from every ready store with room for its allocation bound, starting with the store in which
the module starts.  When the gate accepts, the covariance is positive definite, `[lo, hi]`
contains the squared Mahalanobis distance, and the verdict compares it with the threshold. -/
theorem gate_module :
    (∃ bytes, Wasm.Encoding.encode gateCompiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok gateCompiled.module) ∧
      ({ name := "gate", funcIdx := 30 } : Wasm.Export) ∈ gateCompiled.module.exports ∧
      _root_.Verified.Ready gateCompiled.module gateCompiled.tables
        (_root_.Verified.initialHeap gateCompiled.tables) gateCompiled.module.initialStore ∧
      _root_.Verified.CallSpec gateCompiled.module gateCompiled.tables 30
        (fun x : Array Float × Array Float × Float => gate x.1 x.2.1 x.2.2)
        gateCompiled.gate.bound ∧
      ∀ (nu s : Array Float) (g : Float), nu.size < 2 ^ 64 ∧ s.size < 2 ^ 64 →
        (gate nu s g).status = 0 →
        (covariance s nu.size).PosDef ∧
          value (gate nu s g).lo.toBits ≤ Model.mahalanobis (covariance s nu.size) (innovation nu) ∧
          Model.mahalanobis (covariance s nu.size) (innovation nu) ≤ value (gate nu s g).hi.toBits ∧
          ((gate nu s g).verdict = 1 →
            Model.mahalanobis (covariance s nu.size) (innovation nu) ≤ value g.toBits) ∧
          ((gate nu s g).verdict = 2 →
            value g.toBits < Model.mahalanobis (covariance s nu.size) (innovation nu)) := by
  obtain ⟨bytes, henc, hdec, _⟩ := gateCompiled.bytes
  refine ⟨⟨bytes, henc, hdec⟩, gate_export,
    _root_.Verified.Ready.initial rfl gateCompiled.initial, gate_callSpec, fun nu s g hs h => ?_⟩
  obtain ⟨-, -, -, -, -, hpd, -, -, hlo, hhi, h1, h2⟩ := gate_sound hs h
  exact ⟨hpd, hlo, hhi, h1, h2⟩

#print axioms gate_callSpec
#print axioms gate_module

end Demos.Gate
