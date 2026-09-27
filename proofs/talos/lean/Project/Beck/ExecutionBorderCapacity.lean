import Project.Beck.ExecutionBorderAllocate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem border_push_capacity_shape : (borderEligible.drop 18).take 54 =
    FixedArrayCapacity.localProgram 43 1 49 ++ (borderEligible.drop 36).take 36 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem borderPushCapacity_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : BorderSaved) (paramsLength : params.length = 10)
    (pointer : UInt64) (words : Array UInt64) (value : UInt64)
    (target counter padding47 padding48 oldNeed previous current capacity next result : UInt64)
    (remaining pageLimit : Nat) (represented : UInt64Array.At initial pointer words)
    (protectedWords : heap.Protects pointer.toNat (pointer.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size < 56)
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (words.size + 2))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (words.push value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (borderPushFrame params saved pointer words.size node.root words.size.toUInt64 value padding47 padding48
          need previous current capacity next node.root) env) :
    wp Project.Beck.«module» ((borderEligible.drop 18).take 54 ++ rest) Q initial
      (borderPushFrame params saved pointer words.size target counter value padding47 padding48
        oldNeed previous current capacity next result) env := by
  rw [border_push_capacity_shape, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 43 (words.size + 1).toUInt64 1 49 Project.Beck.«module» env initial _
  · simp only [borderPushFrame, borderPrefix, Locals.get, paramsLength, List.cons_append, List.nil_append,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  · rfl
  · simp [borderPushFrame, paramsLength]
  · simp [Locals.validIndex, borderPushFrame, borderPrefix, paramsLength]
  · rw [words_capacity (words.size + 1) (by omega)]
    have execute := borderPushAllocated_owned env initial heap params saved paramsLength pointer words value
      target counter padding47 padding48 previous current capacity next result remaining pageLimit
      represented protectedWords valid bound budget Q rest finish
    simpa only [FixedArrayCapacity.capacityFrame, borderPushFrame, borderPrefix, paramsLength,
      List.cons_append, List.nil_append, Locals.set, List.set, List.length, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      reduceIte, Nat.add_assoc] using execute

set_option maxRecDepth 2048 in
theorem border_column_push_shape : (borderEligible.drop 94).take 54 = (borderEligible.drop 18).take 54 := rfl

#print axioms borderPushCapacity_owned

end Project.Beck.Execution
