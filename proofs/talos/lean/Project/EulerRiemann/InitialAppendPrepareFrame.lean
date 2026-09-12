import Project.EulerRiemann.InitialAppendInput
import Project.ProofKit.FixedArraySearchPrepare

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold

def initialAppendInputSaved (saved : List Wasm.Value)
    (n size source upper left right : UInt64) : List Wasm.Value :=
  let pointers := (((((saved.set 30 (.i64 upper)).set 31 (.i64 upper)).set 32 (.i64 n)).set 33
    (.i64 size)).set 43 (.i64 source)).set 44 (.i64 upper)
  let lengths := (pointers.set 45 (.i64 left)).set 46 (.i64 right)
  ((lengths.set 47 (.i64 (left + right))).set 48 (.i64 (left * 7))).set 49 (.i64 (right * 7))

theorem initial_append_input_saved_length (saved : List Wasm.Value)
    (n size source upper left right : UInt64) :
    (initialAppendInputSaved saved n size source upper left right).length = saved.length := by
  simp [initialAppendInputSaved]

theorem initial_append_input_gets (frame : Locals) (n size source upper left right : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61) :
    (initialAppendInputFrame frame n size source upper left right).get 48 = some (.i64 source) ∧
    (initialAppendInputFrame frame n size source upper left right).get 49 = some (.i64 upper) ∧
    (initialAppendInputFrame frame n size source upper left right).get 52 = some (.i64 (left + right)) ∧
    (initialAppendInputFrame frame n size source upper left right).get 53 = some (.i64 (left * 7)) ∧
    (initialAppendInputFrame frame n size source upper left right).get 54 = some (.i64 (right * 7)) := by
  simp only [initialAppendInputFrame, initialAppendLengthFrame, initialAppendPointersFrame,
    initialAppendCountsFrame, resultFrame_get_ne, resultFrame_params, hParams,
    Nat.reduceLeDiff, ne_eq, Nat.reduceEqDiff, not_false_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply resultFrame_get_result <;>
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hParams, hLocals]

theorem initial_append_input_frame_eq (params saved tail : List Wasm.Value)
    (need previous current capacity next result n size source upper left right : UInt64)
    (hParams : params.length = 5) (hSaved : saved.length = 54) :
    initialAppendInputFrame
      (FixedArraySearch.frame params saved tail need previous current capacity next result)
      n size source upper left right =
    FixedArraySearch.frame params (initialAppendInputSaved saved n size source upper left right) tail
      need previous current capacity next result := by
  simp [initialAppendInputFrame, initialAppendLengthFrame, initialAppendPointersFrame,
    initialAppendCountsFrame, initialAppendInputSaved, FixedArraySearch.resultFrame_before, hParams, hSaved]

theorem initial_append_capacity_frame_eq (params saved tail : List Wasm.Value)
    (need previous current capacity next result n size source upper left right : UInt64)
    (hParams : params.length = 5) (hSaved : saved.length = 54) :
    FixedArrayCapacity.capacityFrame (initialAppendInputFrame
      (FixedArraySearch.frame params saved tail need previous current capacity next result)
      n size source upper left right) 59 (FixedArrayCapacity.normalizedCapacity (left + right) 7) =
    FixedArraySearch.frame params (initialAppendInputSaved saved n size source upper left right) tail
      (FixedArrayCapacity.normalizedCapacity (left + right) 7) previous current capacity next result := by
  rw [initial_append_input_frame_eq params saved tail need previous current capacity next result
    n size source upper left right hParams hSaved]
  have h := FixedArraySearch.capacityFrame_need params
    (initialAppendInputSaved saved n size source upper left right) tail need previous current capacity next result
    (FixedArrayCapacity.normalizedCapacity (left + right) 7)
  simpa only [initial_append_input_saved_length, hParams, hSaved, Nat.reduceAdd] using h

#print axioms initial_append_input_gets
#print axioms initial_append_input_frame_eq
#print axioms initial_append_capacity_frame_eq

end Project.EulerRiemann.Execution
