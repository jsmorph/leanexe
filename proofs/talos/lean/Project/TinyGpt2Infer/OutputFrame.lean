import Project.TinyGpt2.Model
import Project.ProofKit.I64LocalRange
import Project.ProofKit.FixedArraySearchProjection

namespace Project.TinyGpt2Infer.Spec
open Wasm Project.TinyGpt2 Project.ProofKit FixedArrayFold

def savedOutputLocals : List Nat := [0, 16, 17, 18, 19, 21, 46, 47]

structure OutputSaved (pointer empty : UInt64) (x : Row) (frame : Locals) : Prop where
  params : frame.params.length = 5
  locals : frame.locals.length = 62
  values : frame.values = []
  pointer : frame.get 0 = some (.i64 pointer)
  x0 : frame.get 16 = some (.i64 x.x0)
  x1 : frame.get 17 = some (.i64 x.x1)
  x2 : frame.get 18 = some (.i64 x.x2)
  x3 : frame.get 19 = some (.i64 x.x3)
  empty : frame.get 21 = some (.i64 empty)
  limit : frame.get 46 = some (.i64 256)
  step : frame.get 47 = some (.i64 1)
  scratch : I64LocalRange frame 57 63

theorem OutputSaved.valid {pointer empty : UInt64} {x : Row} {frame : Locals}
    (h : OutputSaved pointer empty x frame) (index : Nat) (hIndex : index < 67) :
    frame.validIndex index := by
  simpa only [Locals.validIndex, h.params, h.locals] using hIndex

theorem OutputSaved.transport {pointer empty : UInt64} {x : Row} {frame next : Locals}
    (h : OutputSaved pointer empty x frame)
    (hParams : next.params.length = frame.params.length)
    (hLocals : next.locals.length = frame.locals.length)
    (hValues : next.values = [])
    (hGets : ∀ index ∈ savedOutputLocals, next.get index = frame.get index)
    (hScratch : I64LocalRange next 57 63) : OutputSaved pointer empty x next := by
  exact ⟨hParams.trans h.params, hLocals.trans h.locals, hValues,
    (hGets 0 (by decide)).trans h.pointer,
    (hGets 16 (by decide)).trans h.x0, (hGets 17 (by decide)).trans h.x1,
    (hGets 18 (by decide)).trans h.x2, (hGets 19 (by decide)).trans h.x3,
    (hGets 21 (by decide)).trans h.empty, (hGets 46 (by decide)).trans h.limit,
    (hGets 47 (by decide)).trans h.step, hScratch⟩

theorem OutputSaved.result {pointer empty : UInt64} {x : Row} {frame : Locals}
    (h : OutputSaved pointer empty x frame) (index : Nat) (word : UInt64)
    (hLower : 5 ≤ index) (hUpper : index < 67) (hPreserved : index ∉ savedOutputLocals) :
    OutputSaved pointer empty x (resultFrame frame index word) := by
  have hInternal : frame.params.length ≤ index := by simpa only [h.params] using hLower
  apply h.transport (next := resultFrame frame index word) rfl (resultFrame_locals_length ..) rfl
  · intro read hRead
    exact resultFrame_get_ne frame index read word hInternal (by
      intro hEq
      exact hPreserved (hEq ▸ hRead))
  · exact h.scratch.result index word hInternal (h.valid index hUpper)

theorem OutputSaved.counter {pointer empty : UInt64} {x : Row} {frame : Locals}
    (h : OutputSaved pointer empty x frame) (count : Nat) (hValid : frame.validIndex 53) :
    OutputSaved pointer empty x (FixedArrayCopy.counterFrame frame 53 count hValid) := by
  apply h.transport (FixedArrayCopy.counterFrame_params_length ..)
    (FixedArrayCopy.counterFrame_locals_length ..) rfl
  · intro read hRead
    exact FixedArrayCopy.counterFrame_get_ne frame 53 count read hValid (by
      simp only [savedOutputLocals, List.mem_cons, List.not_mem_nil, or_false] at hRead
      omega)
  · exact h.scratch.counter 53 count hValid

theorem OutputSaved.search {pointer empty : UInt64} {x : Row}
    (params saved tail : List Wasm.Value)
    (need previous current capacity next result : UInt64)
    (h : OutputSaved pointer empty x
      (FixedArraySearch.frame params saved tail need previous current capacity next result))
    (hStart : params.length + saved.length = 57)
    (need' previous' current' capacity' next' result' : UInt64) :
    OutputSaved pointer empty x
      (FixedArraySearch.frame params saved tail need' previous' current' capacity' next' result') := by
  apply h.transport
    (next := FixedArraySearch.frame params saved tail need' previous' current' capacity' next' result')
    rfl (by simp only [FixedArraySearch.frame, List.length_append, List.length_cons]) rfl
  · intro read hRead
    have hReadBound : read < params.length + saved.length := by
      simp only [savedOutputLocals, List.mem_cons, List.not_mem_nil, or_false] at hRead
      omega
    rw [FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ read hReadBound,
      FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ read hReadBound]
  · exact h.scratch.search need' previous' current' capacity' next' result'

#print axioms OutputSaved.transport
#print axioms OutputSaved.result
#print axioms OutputSaved.counter
#print axioms OutputSaved.search
end Project.TinyGpt2Infer.Spec
