import Project.Beck.ExecutionMatrixAllocate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem matrix_push_capacity_shape : (matrixRowBody.drop 50).take 54 =
    FixedArrayCapacity.localProgram 75 1 81 ++ (matrixRowBody.drop 68).take 36 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixPushCapacity_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : MatrixSaved) (paramsLength : params.length = 9)
    (pointer : UInt64) (words : Array UInt64) (value : UInt64)
    (target counter padding79 padding80 oldNeed previous current capacity next result : UInt64) (after : MatrixAfter)
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
        (matrixPushFrame params saved pointer words.size node.root words.size.toUInt64 value padding79 padding80
          need previous current capacity next node.root after) env) :
    wp Project.Beck.«module» ((matrixRowBody.drop 50).take 54 ++ rest) Q initial
      (matrixPushFrame params saved pointer words.size target counter value padding79 padding80
        oldNeed previous current capacity next result after) env := by
  rw [matrix_push_capacity_shape, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 75 (words.size + 1).toUInt64 1 81 Project.Beck.«module» env initial _
  · simp only [matrixPushFrame, matrixPrefix, matrixSuffix, Locals.get, paramsLength, List.cons_append, List.nil_append,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  · rfl
  · simp [matrixPushFrame, paramsLength]
  · simp [Locals.validIndex, matrixPushFrame, matrixPrefix, matrixSuffix, paramsLength]
  · rw [words_capacity (words.size + 1) (by omega)]
    have execute := matrixPushAllocated_owned env initial heap params saved paramsLength pointer words value
      target counter padding79 padding80 previous current capacity next result after remaining pageLimit
      represented protectedWords valid bound budget Q rest finish
    simpa only [FixedArrayCapacity.capacityFrame, matrixPushFrame, matrixPrefix, matrixSuffix, paramsLength,
      List.cons_append, List.nil_append, Locals.set, List.set, List.length, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      reduceIte, Nat.add_assoc] using execute

#print axioms matrixPushCapacity_owned

end Project.Beck.Execution
