import Project.EulerRiemann.FrozenInitialExtractInput
import Project.ProofKit.FixedArraySearchPrepare

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialExtractInputSaved (saved : List Wasm.Value) (source size length : UInt64) : List Wasm.Value :=
  let loaded := (((saved.set 43 (.i64 source)).set 44 (.i64 0)).set 45 (.i64 size)).set 46 (.i64 length)
  (((loaded.set 47 (.i64 size)).set 48 (.i64 size)).set 49 (.i64 0)).set 50 (.i64 (size * 7))

theorem initial_extract_input_saved_length (saved : List Wasm.Value) (source size length : UInt64) :
    (initialExtractInputSaved saved source size length).length = saved.length := by
  simp [initialExtractInputSaved]

theorem initial_extract_input_frame_eq (params saved : List Wasm.Value)
    (need previous current capacity next result source size length : UInt64)
    (hParams : params.length = 5) (hSaved : saved.length = 55) :
    initialExtractInputFrame
      (FixedArraySearch.frame params saved [] need previous current capacity next result) source size length =
    FixedArraySearch.frame params (initialExtractInputSaved saved source size length) []
      need previous current capacity next result := by
  simp [initialExtractInputFrame, initialExtractCountsFrame, initialExtractLoadFrame,
    initialExtractPointersFrame, initialExtractInputSaved, FixedArraySearch.resultFrame_before, hParams, hSaved]

theorem initial_extract_capacity_frame_eq (params saved : List Wasm.Value)
    (need previous current capacity next result source size length : UInt64)
    (hParams : params.length = 5) (hSaved : saved.length = 55) :
    FixedArrayCapacity.capacityFrame (initialExtractInputFrame
      (FixedArraySearch.frame params saved [] need previous current capacity next result) source size length)
      60 (FixedArrayCapacity.normalizedCapacity size 7) =
    FixedArraySearch.frame params (initialExtractInputSaved saved source size length) []
      (FixedArrayCapacity.normalizedCapacity size 7) previous current capacity next result := by
  rw [initial_extract_input_frame_eq params saved need previous current capacity next result
    source size length hParams hSaved]
  have h := FixedArraySearch.capacityFrame_need params (initialExtractInputSaved saved source size length) []
    need previous current capacity next result (FixedArrayCapacity.normalizedCapacity size 7)
  simpa only [initial_extract_input_saved_length, hParams, hSaved, Nat.reduceAdd] using h

#print axioms initial_extract_input_frame_eq
#print axioms initial_extract_capacity_frame_eq

end Project.EulerRiemann.Frozen.Execution
