import Demos.Gate.GateVerified
import Demos.Gate.GateSoundness
import Verified.Call
import Verified.BoundFacts

/-! The call of the module's export `gate`.  The program allocates the arrays of its elimination,
and `gate_bound` bounds the generated allocation bound by 6,496,880 bytes, so the call returns
without a trap from a ready store in which the allocator's `top` can rise by that much, and `top`
rises by at most that much.
`gate_module` joins the module's bytes, the export, the readiness of the start store, the call,
and the conclusions of `gate_sound` for accepted results. -/

namespace Demos.Gate

open CodeLib.IEEE64 (value Finite)

theorem gate_export :
    ({ name := "gate", funcIdx := 30 } : Wasm.Export) ∈ gateCompiled.module.exports := by
  decide +kernel

/-- Each step of the elimination keeps the sizes of the matrix and the right-hand side. -/
theorem elimStep_sizes {d k : UInt64} {e : Elim} (ha : e.a.size = (d * d).toNat)
    (hr : e.r.size = d.toNat) :
    (elimStep d k e).a.size = (d * d).toNat ∧ (elimStep d k e).r.size = d.toNat := by
  unfold elimStep
  dsimp only
  split
  · split
    · exact ⟨LeanExe.Dialect.build_size _ _, LeanExe.Dialect.build_size _ _⟩
    · exact ⟨ha, hr⟩
  · exact ⟨ha, hr⟩

/-- The gate raises the allocator's `top` by at most `(d + 1) (24 d² + 24 d + 112)` bytes for
`d ≤ 64`, which is at most 6,496,880 bytes. -/
theorem gate_bound (x : Array Float × Array Float × Float) :
    gateCompiled.gate.bound x ≤ 6496880 := by
  obtain ⟨nu, s, g⟩ := x
  rw [gateCompiled.gate.bound_eq]
  split
  · rename_i h1
    simp only [decide_eq_true_eq] at h1
    obtain ⟨-, h64, -⟩ := h1
    have hd : nu.size.toUInt64.toNat ≤ 64 := UInt64.le_iff_toNat_le.mp h64
    split
    · set d := nu.size.toUInt64
      have hdd : (d * d).toNat = d.toNat * d.toNat := by
        rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by nlinarith)]
      rw [gateCompiled.eliminate.bound_eq]
      have hloop := Verified.loopCost_le (CA := fun _ => 0) (C := fun _ => true)
        (BA := fun a b => gateCompiled.elimStep.bound (d, a, b))
        (F := fun k e => elimStep d k e) (P := fun _ (e : Elim) =>
          e.a.size = (d * d).toNat ∧ e.r.size = d.toNat)
        (cost := fun _ => Verified.blockCost ((d * d).toNat * 3) + Verified.blockCost (d.toNat * 3))
        (fun k e he => by
          rw [gateCompiled.elimStep.bound_eq]
          simp only [Nat.zero_add, ↓reduceIte]
          split
          · split
            · exact le_rfl
            · rw [he.1, he.2]
          · rw [he.1, he.2])
        (fun k e he _ => elimStep_sizes he.1 he.2) (n := d.toNat)
        (I := ⟨0, LeanExe.build (d * d) fun t => Library.Numerics.Interval.point s[t.toNat]!,
          LeanExe.build d fun i => Library.Numerics.Interval.point nu[i.toNat]!,
          Library.Numerics.Interval.point 0.0⟩)
        ⟨LeanExe.Dialect.build_size _ _, LeanExe.Dialect.build_size _ _⟩
      rw [Verified.sumBelow_const] at hloop
      have hc : Verified.blockCost ((d * d).toNat * 3) + Verified.blockCost (d.toNat * 3) ≤
          99952 := by
        rw [Verified.blockCost_eq, Verified.blockCost_eq, hdd]
        have := Nat.mul_le_mul hd hd
        omega
      have hm := Nat.mul_le_mul hd hc
      omega
    · omega
  · omega

/-- The module's export computes `gate` without a trap whenever `top` can rise by 6,496,880
bytes within the memory's cap, and raises `top` by at most that much. -/
theorem gate_trapFree : LeanExe.Pipeline.ImplementsA false gateCompiled.module 30
    (fun x : Array Float × Array Float × Float => gate x.1 x.2.1 x.2.2)
    (fun _ heap store => heap.Within store gateCompiled.module 6496880)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 6496880) :=
  gateCompiled.gate.trapFree.mono (fun x _ _ h => h.mono (gate_bound x))
    fun x _ _ _ _ _ h => h.trans (Nat.add_le_add_left (gate_bound x) _)

set_option maxRecDepth 100000 in
/-- The export `gate` returns `gate nu s g` without a trap from every ready store with room for
6,496,880 bytes. -/
theorem gate_callSpec :
    _root_.Verified.CallSpec gateCompiled.module gateCompiled.tables 30
      (fun x : Array Float × Array Float × Float => gate x.1 x.2.1 x.2.2) fun _ => 6496880 :=
  _root_.Verified.ImplementsTables.call (_root_.Verified.ImplementsTables.ofA gate_trapFree)
    gateCompiled.tables nofun

/-- The module's bytes decode to the module, whose export `gate` returns `gate nu s g` without a
trap from every ready store with room for 6,496,880 bytes, starting with the store in which
the module starts.  When the gate accepts, the covariance is positive definite, `[lo, hi]`
contains the squared Mahalanobis distance, and the verdict compares it with the threshold. -/
theorem gate_module :
    (∃ bytes, Wasm.Encoding.encode gateCompiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok gateCompiled.module) ∧
      ({ name := "gate", funcIdx := 30 } : Wasm.Export) ∈ gateCompiled.module.exports ∧
      _root_.Verified.Ready gateCompiled.module gateCompiled.tables
        (_root_.Verified.initialHeap gateCompiled.tables) gateCompiled.module.initialStore ∧
      _root_.Verified.CallSpec gateCompiled.module gateCompiled.tables 30
        (fun x : Array Float × Array Float × Float => gate x.1 x.2.1 x.2.2) (fun _ => 6496880) ∧
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

#print axioms gate_bound
#print axioms gate_trapFree
#print axioms gate_callSpec
#print axioms gate_module

end Demos.Gate
