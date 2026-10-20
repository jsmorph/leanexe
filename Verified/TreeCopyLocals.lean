import Verified.LocalFrame

namespace Verified

open Wasm

structure CopyLocals (base : Nat) (initial : Locals) (result current : UInt64)
    (s : Locals) : Prop where
  frame : Frame base initial s
  result : s.get base = some (.i64 result)
  current : s.get (base + 1) = some (.i64 current)
  values : s.values = initial.values

theorem CopyLocals.scratch {base index : Nat} {initial s : Locals} {result current : UInt64}
    {value : Value} (h : CopyLocals base initial result current s)
    (hLow : s.params.length ≤ index) (hIndex : base + 2 ≤ index) (hHigh : index < s.positions) :
    CopyLocals base initial result current (setLocal s index value) := by
  refine ⟨h.frame.trans (Frame.set hLow (by omega) hHigh), ?_, ?_, h.values⟩
  · rw [Locals.get_setLocal_ne hLow (by omega)]
    exact h.result
  · rw [Locals.get_setLocal_ne hLow (by omega)]
    exact h.current

theorem CopyLocals.setCurrent {base : Nat} {initial s : Locals} {result current next : UInt64}
    (h : CopyLocals base initial result current s) (hLow : s.params.length ≤ base + 1)
    (hHigh : base + 1 < s.positions) :
    CopyLocals base initial result next (setLocal s (base + 1) (.i64 next)) := by
  refine ⟨h.frame.trans (Frame.set hLow (by omega) hHigh), ?_, ?_, h.values⟩
  · rw [Locals.get_setLocal_ne hLow (by omega)]
    exact h.result
  · exact Locals.get_setLocal_same hLow (Locals.lt_total hHigh)

theorem CopyLocals.ofRead {base : Nat} {initial s s' : Locals} {result current : UInt64}
    (h : CopyLocals base initial result current s) (hFrame : Frame base s s')
    (hResult : s'.get base = s.get base) (hCurrent : s'.get (base + 1) = some (.i64 current))
    (hValues : s'.values = s.values) : CopyLocals base initial result current s' :=
  ⟨h.frame.trans hFrame, hResult.trans h.result, hCurrent, hValues.trans h.values⟩

#print axioms CopyLocals.scratch
#print axioms CopyLocals.setCurrent

end Verified
