import Project.ProofKit.FixedArrayFrame
import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.FixedArraySearchWindow

namespace Project.ProofKit
open Wasm FixedArrayFold FixedArrayCopy

def I64LocalRange (frame : Locals) (first last : Nat) : Prop :=
  ∀ index : Nat, first ≤ index → index < last → ∃ word : UInt64, frame.get index = some (.i64 word)

theorem I64LocalRange.of_preserved {base frame : Locals} {first last : Nat}
    (h : I64LocalRange base first last)
    (hGets : ∀ index : Nat, first ≤ index → index < last → frame.get index = base.get index) :
    I64LocalRange frame first last := by
  intro index hFirst hLast
  rw [hGets index hFirst hLast]
  exact h index hFirst hLast

theorem I64LocalRange.result {frame : Locals} {first last : Nat}
    (h : I64LocalRange frame first last) (index : Nat) (word : UInt64)
    (hInternal : frame.params.length ≤ index) (hValid : frame.validIndex index) :
    I64LocalRange (resultFrame frame index word) first last := by
  intro other hFirst hLast
  by_cases hEq : other = index
  · subst other
    exact ⟨word, resultFrame_get_result frame index word hInternal hValid⟩
  · rw [resultFrame_get_ne frame index other word hInternal hEq]
    exact h other hFirst hLast

theorem I64LocalRange.counter {frame : Locals} {first last : Nat}
    (h : I64LocalRange frame first last) (index count : Nat) (hValid : frame.validIndex index) :
    I64LocalRange (counterFrame frame index count hValid) first last := by
  intro other hFirst hLast
  by_cases hEq : other = index
  · subst other
    exact ⟨UInt64.ofNat count, counterFrame_get_counter ..⟩
  · rw [counterFrame_get_ne frame index count other hValid hEq]
    exact h other hFirst hLast

theorem I64LocalRange.window {frame : Locals} {first last : Nat}
    (h : I64LocalRange frame first last) (offset : Nat)
    (hFirst : first ≤ frame.params.length + offset)
    (hLast : frame.params.length + offset + 6 ≤ last)
    (hBound : offset + 6 ≤ frame.locals.length) (hValues : frame.values = []) :
    ∃ need previous current capacity next result : UInt64,
      frame = FixedArraySearch.frame frame.params (frame.locals.take offset)
        (frame.locals.drop (offset + 6)) need previous current capacity next result := by
  have hWord (i : Nat) (hi : i < 6) :=
    h (frame.params.length + offset + i) (by omega) (by omega)
  obtain ⟨need, hNeed⟩ := hWord 0 (by decide)
  obtain ⟨previous, hPrevious⟩ := hWord 1 (by decide)
  obtain ⟨current, hCurrent⟩ := hWord 2 (by decide)
  obtain ⟨capacity, hCapacity⟩ := hWord 3 (by decide)
  obtain ⟨next, hNext⟩ := hWord 4 (by decide)
  obtain ⟨result, hResult⟩ := hWord 5 (by decide)
  refine ⟨need, previous, current, capacity, next, result,
    FixedArraySearch.frame_eq_of_gets frame offset need previous current capacity next result hBound hValues ?_⟩
  intro i hi
  interval_cases i <;> simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] <;> assumption

theorem I64LocalRange.search {params saved tail : List Wasm.Value}
    {need previous current capacity next result : UInt64} {first last : Nat}
    (h : I64LocalRange (FixedArraySearch.frame params saved tail need previous current capacity next result)
      first last)
    (needAfter previousAfter currentAfter capacityAfter nextAfter resultAfter : UInt64) :
    I64LocalRange (FixedArraySearch.frame params saved tail
      needAfter previousAfter currentAfter capacityAfter nextAfter resultAfter) first last := by
  intro index hFirst hLast
  obtain ⟨word, hWord⟩ := h index hFirst hLast
  by_cases hParam : index < params.length
  · exact ⟨word, by simpa [FixedArraySearch.frame, Locals.get, hParam] using hWord⟩
  by_cases hSaved : index - params.length < saved.length
  · exact ⟨word, by simpa [FixedArraySearch.frame, Locals.get, hParam,
      List.getElem?_append, hSaved] using hWord⟩
  by_cases hWindow : index - params.length - saved.length < 6
  · have hIndex : index = params.length + saved.length + (index - params.length - saved.length) := by omega
    rw [hIndex, FixedArraySearch.frame_get _ _ _ _ _ _ _ _ _ _ hWindow]
    interval_cases hField : index - params.length - saved.length <;> simp
  · exact ⟨word, by simpa only [FixedArraySearch.frame, Locals.get, hParam, ite_false,
      List.length_append, List.length_cons, List.length_nil, List.getElem?_append,
      hSaved, hWindow] using hWord⟩

#print axioms I64LocalRange.of_preserved
#print axioms I64LocalRange.result
#print axioms I64LocalRange.counter
#print axioms I64LocalRange.window
#print axioms I64LocalRange.search

end Project.ProofKit
