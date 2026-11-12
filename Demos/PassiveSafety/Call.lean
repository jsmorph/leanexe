import Demos.PassiveSafety.Verified
import Demos.PassiveSafety.Soundness
import Verified.Call

/-! The call of the module's export `check` and its composition with `check_passive`.
`check_call` states that function 86, the export `check`, returns `check xs fuel acc` without a
trap from every ready store, from the generated `compiled.check.implements` and the tables of `sin`
and `cos`, the program's tables 0 and 1.  `passive_safety` joins the module's bytes, the export,
the readiness of the start store, the call, and the bound of `check_passive` for accepted
results. -/

namespace Demos.PassiveSafety

open Model

theorem check_export :
    ({ name := "check", funcIdx := 86 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Function 86 returns, without a trap and from every ready store, the result of the check. -/
theorem check_call :
    _root_.Verified.Call compiled.module compiled.tables 86
      (fun x : Array Float × UInt64 × Float => check x.1 x.2.1 x.2.2) (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) :=
  _root_.Verified.ImplementsTables.call compiled.check.implements compiled.tables
    (_root_.Verified.tables_at [0, 1] (by decide) rfl)

/-- The module's bytes decode to the module, whose export `check` is function 86, whose start
store is ready, and whose entry returns `check xs fuel acc` without a trap from every ready store.
When the check accepts, every trajectory of every scenario from the boxes keeps a separation of at
least `min dmin drc` at every time `t ≥ 0`. -/
theorem passive_safety :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "check", funcIdx := 86 } : Wasm.Export) ∈ compiled.module.exports ∧
      _root_.Verified.Ready compiled.module compiled.tables
        (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      _root_.Verified.Call compiled.module compiled.tables 86
        (fun x : Array Float × UInt64 × Float => check x.1 x.2.1 x.2.2) (fun _ _ _ => True)
        (fun _ _ _ _ _ => True) ∧
      ∀ (xs : Array Float) (fuel : UInt64) (acc : Float), xs.size < 2 ^ 64 →
        (check xs fuel acc).status = 0 →
        ∀ s bs, InBox xs s → Plan xs bs → ∀ j ≤ 2 * bs.length, ∀ t, 0 ≤ t →
          min (val xs 2) (val xs 3) ≤
            separation (path (val xs 0) 0 s (select bs.length j bs) t) := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, check_export,
    _root_.Verified.Ready.initial rfl compiled.initial, check_call,
    fun _ _ _ hs h => check_passive hs h⟩

#print axioms check_call
#print axioms passive_safety

end Demos.PassiveSafety
