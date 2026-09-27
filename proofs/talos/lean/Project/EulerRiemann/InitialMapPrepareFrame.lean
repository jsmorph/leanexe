import Project.EulerRiemann.InitialMapInput
import Project.ProofKit.FixedArraySearchPrepare

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialMapInputSaved (saved : List Wasm.Value) (source length : UInt64) : List Wasm.Value :=
  (((saved.set 43 (.i64 source)).set 5 (.i64 length)).set 43 (.i64 source)).set 44 (.i64 length)

theorem initial_map_input_saved_length (saved : List Wasm.Value) (source length : UInt64) :
    (initialMapInputSaved saved source length).length = saved.length := by
  simp [initialMapInputSaved]

theorem initial_map_input_gets (frame : Locals) (source length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    (initialMapInputFrame frame source length).get 10 = some (.i64 length) ∧
    (initialMapInputFrame frame source length).get 48 = some (.i64 source) ∧
    (initialMapInputFrame frame source length).get 49 = some (.i64 length) := by
  simp only [initialMapInputFrame, resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem initial_map_input_frame_eq (params saved tail : List Wasm.Value)
    (need previous current capacity next result source length : UInt64)
    (hParams : params.length = 5) (hSaved : saved.length = 49) :
    initialMapInputFrame
      (FixedArraySearch.frame params saved tail need previous current capacity next result) source length =
    FixedArraySearch.frame params (initialMapInputSaved saved source length) tail
      need previous current capacity next result := by
  simp [initialMapInputFrame, initialMapInputSaved, FixedArraySearch.resultFrame_before, hParams, hSaved]

theorem initial_map_capacity_frame_eq (params saved tail : List Wasm.Value)
    (need previous current capacity next result source length : UInt64)
    (hParams : params.length = 5) (hSaved : saved.length = 49) :
    FixedArrayCapacity.capacityFrame (initialMapInputFrame
      (FixedArraySearch.frame params saved tail need previous current capacity next result) source length)
      54 (FixedArrayCapacity.normalizedCapacity length 7) =
    FixedArraySearch.frame params (initialMapInputSaved saved source length) tail
      (FixedArrayCapacity.normalizedCapacity length 7) previous current capacity next result := by
  rw [initial_map_input_frame_eq params saved tail need previous current capacity next result
    source length hParams hSaved]
  have h := FixedArraySearch.capacityFrame_need params (initialMapInputSaved saved source length) tail
    need previous current capacity next result (FixedArrayCapacity.normalizedCapacity length 7)
  simpa only [initial_map_input_saved_length, hParams, hSaved, Nat.reduceAdd] using h

#print axioms initial_map_input_gets
#print axioms initial_map_input_frame_eq
#print axioms initial_map_capacity_frame_eq

end Project.EulerRiemann.Execution
