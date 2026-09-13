import Project.EulerRiemann.InitialLoopFrame
import Project.EulerRiemann.InitialMapCursor

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCopy

theorem InitialFrameAt.of_preserved {base frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt base fuel n size source tracker output done)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hPreserved : ∀ index : Nat, index < 9 → frame.get index = base.get index) :
    InitialFrameAt frame fuel n size source tracker output done := by
  have hBaseParams : base.params.length = 5 := by simp [h.params]
  have hParamsEq : frame.params = base.params := by
    apply List.ext_getElem?
    intro index
    by_cases hi : index < 5
    · simpa [Locals.get, hParams, hBaseParams, hi] using hPreserved index (by omega)
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hLocalEq (index : Nat) (hi : index < 4) : frame.locals[index]? = base.locals[index]? := by
    have hGet := hPreserved (5 + index) (by omega)
    have hNotParam : ¬5 + index < 5 := by omega
    have hBound : 5 + index < 5 + 61 := by omega
    simpa only [Locals.get, hParams, hBaseParams, hLocals, h.locals, hNotParam, hBound,
      ite_false, ite_true, Nat.add_sub_cancel_left] using hGet
  exact ⟨hParamsEq.trans h.params, hLocals, hValues,
    (hLocalEq 0 (by decide)).trans h.tracker,
    (hLocalEq 1 (by decide)).trans h.outputOwner,
    (hLocalEq 2 (by decide)).trans h.outputPointer,
    (hLocalEq 3 (by decide)).trans h.done⟩

theorem InitialFrameAt.result {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done)
    (index : Nat) (value : UInt64) (hi : 9 ≤ index) :
    InitialFrameAt (resultFrame frame index value) fuel n size source tracker output done := by
  have hParams : frame.params.length = 5 := by simp [h.params]
  apply h.of_preserved (frame := resultFrame frame index value) hParams
    (by simpa only [resultFrame_locals_length] using h.locals) rfl
  intro other hOther
  exact resultFrame_get_ne frame index other value (by omega) (by omega)

theorem InitialFrameAt.counter {frame : Locals} {fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt frame fuel n size source tracker output done)
    (index count : Nat) (hValid : frame.validIndex index) (hi : 9 ≤ index) :
    InitialFrameAt (counterFrame frame index count hValid) fuel n size source tracker output done := by
  have hParams : frame.params.length = 5 := by simp [h.params]
  apply h.of_preserved (by simpa only [counterFrame_params_length] using hParams)
    (by simpa only [counterFrame_locals_length] using h.locals) rfl
  intro other hOther
  exact counterFrame_get_ne frame index count other hValid (by omega)

theorem InitialFrameAt.mapped {base frame : Locals} {fuel : UInt64} {n size count : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt base fuel n size source tracker output done)
    (hMap : InitialMapFrameAt base count frame) :
    InitialFrameAt frame fuel n size source tracker output done := by
  apply h.of_preserved hMap.paramsLength hMap.localsLength hMap.values
  intro index hi
  exact hMap.preserved index (by omega) (by omega) (by omega)

#print axioms InitialFrameAt.of_preserved
#print axioms InitialFrameAt.result
#print axioms InitialFrameAt.counter
#print axioms InitialFrameAt.mapped

end Project.EulerRiemann.Execution
