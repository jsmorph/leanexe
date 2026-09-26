import Project.EulerRiemann.FrozenInitialAllocationFrame
import Project.EulerRiemann.FrozenInitialContinue
import Project.ProofKit.I64LocalRange

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayCopy

abbrev InitialScratch (frame : Locals) : Prop := I64LocalRange frame 54 66

theorem InitialScratch.selected {frame : Locals} (h : InitialScratch frame)
    (source : UInt64) (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    InitialScratch (initialSelectedFrame frame source) :=
  h.result 48 source (by omega) (by simp [Locals.validIndex, hParams, hLocals])

theorem InitialScratch.mapInput {frame : Locals} (h : InitialScratch frame)
    (source length : UInt64) (hParams : frame.params.length = 5) :
    InitialScratch (initialMapInputFrame frame source length) := by
  apply h.of_preserved
  intro index hFirst hLast
  exact initial_map_input_get_other frame source length index hParams (by omega) (by omega) (by omega)

theorem InitialScratch.mapAllocated {params saved tail : List Wasm.Value}
    {need previous current capacity next result : UInt64}
    (h : InitialScratch (FixedArraySearch.frame params saved tail need previous current capacity next result))
    (hParams : params.length = 5) (hSaved : saved.length = 49) (hTail : tail.length = 6)
    (source length base requested previousAfter : UInt64) :
    InitialScratch (initialMapAllocationReady params (initialMapInputSaved saved source length) tail
      base requested previousAfter (by rw [initial_map_input_saved_length, hParams, hSaved])) := by
  have hInput := h.mapInput source length hParams
  rw [initial_map_input_frame_eq _ _ _ _ _ _ _ _ _ _ _ hParams hSaved] at hInput
  have hSearch := hInput.search requested previousAfter 0 (base + 48 + requested)
    ((base + 48 + requested - 1) / 65536 + 1) (base + 48)
  apply (hSearch.result 50 (base + 48) (by simp [FixedArraySearch.frame, hParams]) ?_).counter
  simp [Locals.validIndex, FixedArraySearch.frame, initial_map_input_saved_length, hParams, hSaved, hTail]

theorem InitialMapFrameAt.scratchTail {base frame : Locals} {count : Nat}
    (h : InitialMapFrameAt base count frame) (hScratch : InitialScratch base) :
    I64LocalRange frame 57 66 := by
  intro index hFirst hLast
  rw [h.preserved index (by omega) (by omega) (by omega)]
  exact hScratch index (by omega) hLast

theorem initial_append_input_scratchTail {frame : Locals}
    (h : I64LocalRange frame 57 66) (n size source upper left right : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    I64LocalRange (initialAppendInputFrame frame n size source upper left right) 57 66 := by
  unfold initialAppendInputFrame initialAppendLengthFrame initialAppendPointersFrame initialAppendCountsFrame
  repeat first
    | apply I64LocalRange.result
    | exact h
    | (simp only [resultFrame_params, resultFrame_locals_length, Locals.validIndex, hParams, hLocals]; omega)

theorem initial_append_done_gets (params saved tail : List Wasm.Value)
    (hParams : params.length = 5) (hSaved : saved.length = 54) (hTail : tail.length = 1)
    (n size source upper left right base requested previousAfter : UInt64) (count : Nat) :
    let frame := initialAppendAllocationDone params
      (initialAppendInputSaved saved n size source upper left right) tail base requested previousAfter count
      (by rw [initial_append_input_saved_length, hParams, hSaved])
    frame.get 37 = some (.i64 n) ∧ frame.get 38 = some (.i64 size) ∧
      frame.get 54 = some (.i64 (right * 7)) ∧ frame.get 55 = some (.i64 (base + 48)) := by
  dsimp only
  simp [initialAppendAllocationDone, initialAppendAllocationFrame, FixedArraySearch.frame,
    initialAppendInputSaved, hParams, hSaved, hTail, Locals.get, resultFrame, counterFrame, Locals.set]

theorem initial_append_allocated_scratch {params saved tail : List Wasm.Value}
    {need previous current capacity next result : UInt64}
    (h : I64LocalRange (FixedArraySearch.frame params saved tail need previous current capacity next result) 57 66)
    (hParams : params.length = 5) (hSaved : saved.length = 54) (hTail : tail.length = 1)
    (n size source upper left right base requested previousAfter : UInt64) (count : Nat) :
    InitialScratch (initialAppendAllocationDone params
      (initialAppendInputSaved saved n size source upper left right) tail base requested previousAfter count
      (by rw [initial_append_input_saved_length, hParams, hSaved])) := by
  have hLocals : (FixedArraySearch.frame params saved tail need previous current capacity next result).locals.length = 61 := by
    simp [FixedArraySearch.frame, hSaved, hTail]
  have hInput := initial_append_input_scratchTail h n size source upper left right hParams hLocals
  rw [initial_append_input_frame_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hParams hSaved] at hInput
  have hSearch := hInput.search requested previousAfter 0 (base + 48 + requested)
    ((base + 48 + requested - 1) / 65536 + 1) (base + 48)
  have hValid : (FixedArraySearch.frame params
      (initialAppendInputSaved saved n size source upper left right) tail requested previousAfter 0
      (base + 48 + requested) ((base + 48 + requested - 1) / 65536 + 1) (base + 48)).validIndex 55 := by
    simp [Locals.validIndex, FixedArraySearch.frame, initial_append_input_saved_length, hParams, hSaved, hTail]
  have hTailAfter := (hSearch.result 55 (base + 48) (by simp [FixedArraySearch.frame, hParams]) hValid).counter
    56 (7 * count) (by simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length,
      FixedArraySearch.frame, initial_append_input_saved_length, hParams, hSaved, hTail])
  have hGets := initial_append_done_gets params saved tail hParams hSaved hTail
    n size source upper left right base requested previousAfter count
  intro index hFirst hLast
  by_cases hHigh : 57 ≤ index
  · exact hTailAfter index hHigh hLast
  · interval_cases index
    · exact ⟨right * 7, hGets.2.2.1⟩
    · exact ⟨base + 48, hGets.2.2.2⟩
    · exact ⟨UInt64.ofNat (7 * count), counterFrame_get_counter ..⟩

theorem InitialScratch.continued {frame : Locals} (h : InitialScratch frame)
    (fuel : UInt64) (n size : Nat) (root : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    InitialScratch (initialContinuedFrame frame fuel n size root) := by
  apply h.of_preserved
  intro index hFirst hLast
  simp (disch := omega) [initialContinuedFrame, Locals.get, hParams, hLocals,
    show ¬index < 5 by omega, hLast]

#print axioms InitialScratch.selected
#print axioms InitialScratch.mapInput
#print axioms InitialScratch.mapAllocated
#print axioms InitialMapFrameAt.scratchTail
#print axioms initial_append_input_scratchTail
#print axioms initial_append_done_gets
#print axioms initial_append_allocated_scratch
#print axioms InitialScratch.continued

end Project.EulerRiemann.Frozen.Execution
