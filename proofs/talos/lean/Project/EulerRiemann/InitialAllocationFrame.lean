import Project.EulerRiemann.InitialFramePreserve
import Project.EulerRiemann.InitialMapExecute
import Project.EulerRiemann.InitialAppendExecute
import Project.EulerRiemann.InitialExtractExecute

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCopy

theorem InitialFrameAt.search {params saved tail : List Wasm.Value}
    {need previous current capacity next result fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt
      (FixedArraySearch.frame params saved tail need previous current capacity next result)
      fuel n size source tracker output done)
    (savedAfter tailAfter : List Wasm.Value)
    (needAfter previousAfter currentAfter capacityAfter nextAfter resultAfter : UInt64)
    (hSaved : 4 ≤ saved.length) (hSavedAfter : savedAfter.length = saved.length)
    (hTailAfter : tailAfter.length = tail.length)
    (hControl : ∀ index : Nat, index < 4 → savedAfter[index]? = saved[index]?) :
    InitialFrameAt
      (FixedArraySearch.frame params savedAfter tailAfter
        needAfter previousAfter currentAfter capacityAfter nextAfter resultAfter)
      fuel n size source tracker output done := by
  have hParams : params.length = 5 := by
    simpa only [FixedArraySearch.frame, List.length_cons, List.length_nil] using congrArg List.length h.params
  apply h.of_preserved (frame := FixedArraySearch.frame params savedAfter tailAfter
    needAfter previousAfter currentAfter capacityAfter nextAfter resultAfter) hParams
    (by simpa only [FixedArraySearch.frame, List.length_append, List.length_cons, List.length_nil,
      hSavedAfter, hTailAfter] using h.locals) rfl
  intro index hi
  rw [FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ _ (by omega),
    FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ _ (by omega)]
  by_cases hParam : index < params.length
  · simp only [Locals.get, hParam, ite_true]
  · have hLocal : index - params.length < 4 := by omega
    simpa only [Locals.get, hParam, ite_false,
      show index < params.length + savedAfter.length by omega,
      show index < params.length + saved.length by omega, ite_true] using hControl _ hLocal

theorem InitialFrameAt.mapAllocated {params saved tail : List Wasm.Value}
    {need previous current capacity next result fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt
      (FixedArraySearch.frame params saved tail need previous current capacity next result)
      fuel n size source tracker output done)
    (hParams : params.length = 5) (hSaved : saved.length = 49)
    (base requested previousAfter length : UInt64) :
    InitialFrameAt (initialMapAllocationReady params (initialMapInputSaved saved source length) tail
      base requested previousAfter (by rw [initial_map_input_saved_length, hParams, hSaved]))
      fuel n size source tracker output done := by
  have hSearch := h.search (initialMapInputSaved saved source length) tail requested previousAfter 0
    (base + 48 + requested) ((base + 48 + requested - 1) / 65536 + 1) (base + 48)
    (by omega) (initial_map_input_saved_length ..) rfl (by
      intro index hi
      simp (disch := omega) [initialMapInputSaved])
  exact (hSearch.result 50 (base + 48) (by decide)).counter 51 0 _ (by decide)

theorem InitialFrameAt.appendAllocated {params saved tail : List Wasm.Value}
    {need previous current capacity next result fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt
      (FixedArraySearch.frame params saved tail need previous current capacity next result)
      fuel n size source tracker output done)
    (hParams : params.length = 5) (hSaved : saved.length = 54)
    (base requested previousAfter upper left right : UInt64) (count : Nat) :
    InitialFrameAt (initialAppendAllocationDone params
      (initialAppendInputSaved saved (UInt64.ofNat n) (UInt64.ofNat size) source upper left right) tail
      base requested previousAfter count (by rw [initial_append_input_saved_length, hParams, hSaved]))
      fuel n size source tracker output done := by
  have hSearch := h.search
    (initialAppendInputSaved saved (UInt64.ofNat n) (UInt64.ofNat size) source upper left right) tail
    requested previousAfter 0 (base + 48 + requested) ((base + 48 + requested - 1) / 65536 + 1)
    (base + 48) (by omega) (initial_append_input_saved_length ..) rfl (by
      intro index hi
      simp (disch := omega) [initialAppendInputSaved])
  exact (hSearch.result 55 (base + 48) (by decide)).counter 56 (7 * count) _ (by decide)

theorem InitialFrameAt.extractAllocated {params saved : List Wasm.Value}
    {need previous current capacity next result fuel : UInt64} {n size : Nat}
    {source tracker output : UInt64} {done : Bool}
    (h : InitialFrameAt
      (FixedArraySearch.frame params saved [] need previous current capacity next result)
      fuel n size source tracker output done)
    (hParams : params.length = 5) (hSaved : saved.length = 55)
    (base requested previousAfter length : UInt64) :
    InitialFrameAt (initialExtractAllocationDone params
      (initialExtractInputSaved saved source (UInt64.ofNat size) length)
      base requested previousAfter size (by rw [initial_extract_input_saved_length, hParams, hSaved]))
      fuel n size source tracker output done := by
  have hSearch := h.search (initialExtractInputSaved saved source (UInt64.ofNat size) length) []
    requested previousAfter 0 (base + 48 + requested) ((base + 48 + requested - 1) / 65536 + 1)
    (base + 48) (by omega) (initial_extract_input_saved_length ..) rfl (by
      intro index hi
      simp (disch := omega) [initialExtractInputSaved])
  exact (hSearch.result 56 (base + 48) (by decide)).counter 57 (7 * size) _ (by decide)

#print axioms InitialFrameAt.search
#print axioms InitialFrameAt.mapAllocated
#print axioms InitialFrameAt.appendAllocated
#print axioms InitialFrameAt.extractAllocated

end Project.EulerRiemann.Execution
