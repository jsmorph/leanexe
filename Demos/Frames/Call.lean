import Demos.Frames.Verified
import Demos.Frames.Soundness
import Verified.Call

/-! The calls of the module's exports and their composition with the soundness theorems.  Each
call theorem states that the export, called from a ready store with represented arguments, returns
the Lean function's result without a trap, from the generated `implements` theorem and the tables
of `sin` and `cos`, the program's tables 0 and 1.  `frames` joins the module's bytes, the exports,
the readiness of the start store, the calls, and the soundness theorems for accepted results. -/

namespace Demos.Frames

open Model

theorem gmst_export :
    ({ name := "gmst", funcIdx := 58 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem temeToEcef_export :
    ({ name := "temeToEcef", funcIdx := 59 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem ready_initial :
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore :=
  _root_.Verified.Ready.initial rfl compiled.initial

set_option maxRecDepth 100000 in
/-- Function 58, the export `gmst`, returns `gmst d lo hi` without a trap from every ready
store. -/
theorem gmst_call :
    _root_.Verified.Call compiled.module compiled.tables 58
      (fun x : UInt64 × Float × Float => gmst x.1 x.2.1 x.2.2) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.gmst.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

set_option maxRecDepth 100000 in
/-- Function 59, the export `temeToEcef`, returns the result of `temeToEcef` without a trap from
every ready store. -/
theorem temeToEcef_call :
    _root_.Verified.Call compiled.module compiled.tables 59
      (fun x : UInt64 × Float × Float × Float × Float × Float × Float × Float × Float × Float ×
          Float × Float × Float =>
        temeToEcef x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
          x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.1
          x.2.2.2.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.temeToEcef.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

/-- The module's bytes decode to the module, whose start store is ready and whose exports `gmst`
and `temeToEcef` return the results of the Lean functions without a trap from every ready store.
An accepted result of `gmst` lies in `[−1, 7]` and encloses the sidereal angle less a whole number
of turns, and an accepted result of `temeToEcef` encloses the Earth-fixed position, as `gmst_sound` and
`temeToEcef_sound` state. -/
theorem frames :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      _root_.Verified.Ready compiled.module compiled.tables
        (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      ({ name := "gmst", funcIdx := 58 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "temeToEcef", funcIdx := 59 } : Wasm.Export) ∈ compiled.module.exports ∧
      (∀ d lo hi, (gmst d lo hi).status = 0 →
        -1 ≤ CodeLib.IEEE64.value (gmst d lo hi).lo.toBits ∧
        CodeLib.IEEE64.value (gmst d lo hi).hi.toBits ≤ 7 ∧ ∃ k : ℤ, ∀ s, Within lo hi s →
          Within (gmst d lo hi).lo (gmst d lo hi).hi
            (gmst82 (julian d.toNat s) - 2 * Real.pi * k)) ∧
      ∀ d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi,
        (temeToEcef d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi).status = 0 →
        ∀ s xp yp x y z, Within slo shi s → Within xplo xphi xp → Within yplo yphi yp →
          Within xlo xhi x → Within ylo yhi y → Within zlo zhi z →
          let r := temeToEcef d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi
          let e := earthFixed (gmst82 (julian d.toNat s)) xp yp (x, y, z)
          Library.Numerics.Interval.Contains r.x e.1 ∧ Library.Numerics.Interval.Contains r.y e.2.1 ∧
            Library.Numerics.Interval.Contains r.z e.2.2 := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, ready_initial, gmst_export, temeToEcef_export,
    fun _ _ _ h => (gmst_sound h).2.2.2.2.2.2, fun _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
      (temeToEcef_sound h).2⟩

#print axioms gmst_call
#print axioms temeToEcef_call
#print axioms frames

end Demos.Frames
