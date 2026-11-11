import Demos.Frames.Verified
import Demos.Frames.Soundness
import Demos.Frames.TimeSound
import Verified.Call

/-! The calls of the module's exports.  Each call theorem states that the export, called from a
ready store with represented arguments, returns the Lean function's result without a trap, from the
generated `implements` theorem and the tables of `sin` and `cos`, the program's tables 0 and 1.
`frames` joins the module's bytes, the readiness of the start store, and the exports, and
`gmst_sound`, `temeToEcef_sound`, `toGeodetic_sound`, `toCartesian_sound`, and `timeScales_sound`
state what an accepted result implies. -/

namespace Demos.Frames

theorem ready_initial :
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore :=
  _root_.Verified.Ready.initial rfl compiled.initial

theorem exports :
    ({ name := "gmst", funcIdx := 83 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "temeToEcef", funcIdx := 84 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "toGeodetic", funcIdx := 85 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "toCartesian", funcIdx := 86 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "timeScales", funcIdx := 82 } : Wasm.Export) ∈ compiled.module.exports := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxRecDepth 100000 in
/-- Function 83, the export `gmst`, returns `gmst d lo hi` without a trap from every ready
store. -/
theorem gmst_call :
    _root_.Verified.Call compiled.module compiled.tables 83
      (fun x : UInt64 × Float × Float => gmst x.1 x.2.1 x.2.2) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.gmst.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

set_option maxRecDepth 100000 in
/-- Function 84, the export `temeToEcef`, returns the result of `temeToEcef` without a trap from
every ready store. -/
theorem temeToEcef_call :
    _root_.Verified.Call compiled.module compiled.tables 84
      (fun x : UInt64 × Float × Float × Float × Float × Float × Float × Float × Float × Float ×
          Float × Float × Float =>
        temeToEcef x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
          x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.1
          x.2.2.2.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2.2.2.2)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.temeToEcef.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

set_option maxRecDepth 100000 in
/-- Function 85, the export `toGeodetic`, returns the result of `toGeodetic` without a trap from
every ready store. -/
theorem toGeodetic_call :
    _root_.Verified.Call compiled.module compiled.tables 85
      (fun x : Float × Float × Float × Float × Float × Float =>
        toGeodetic x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.toGeodetic.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

set_option maxRecDepth 100000 in
/-- Function 86, the export `toCartesian`, returns the result of `toCartesian` without a trap
from every ready store. -/
theorem toCartesian_call :
    _root_.Verified.Call compiled.module compiled.tables 86
      (fun x : Float × Float × Float × Float × Float × Float =>
        toCartesian x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.toCartesian.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

set_option maxRecDepth 100000 in
/-- Function 82, the export `timeScales`, returns the result of `timeScales` without a trap from
every ready store.  It reads no table. -/
theorem timeScales_call :
    _root_.Verified.Call compiled.module compiled.tables 82
      (fun x : Array UInt64 × UInt64 × Float × Float × Float =>
        timeScales x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun _ _ _ => True) (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call
    (_root_.Verified.ImplementsTables.ofA compiled.timeScales.implements) compiled.tables
    (fun _ ht => absurd ht (List.not_mem_nil))

/-- The module's bytes decode to the module, whose start store is ready and whose exports are
functions 82 to 86, which the call theorems cover. -/
theorem frames :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      _root_.Verified.Ready compiled.module compiled.tables
        (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      ({ name := "gmst", funcIdx := 83 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "temeToEcef", funcIdx := 84 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "toGeodetic", funcIdx := 85 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "toCartesian", funcIdx := 86 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "timeScales", funcIdx := 82 } : Wasm.Export) ∈ compiled.module.exports := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, ready_initial, exports⟩

#print axioms gmst_call
#print axioms temeToEcef_call
#print axioms toGeodetic_call
#print axioms toCartesian_call
#print axioms timeScales_call
#print axioms frames

end Demos.Frames
