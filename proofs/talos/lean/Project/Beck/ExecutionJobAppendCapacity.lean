import Project.Beck.ExecutionJobAppend

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem job_append_capacity_shape : (jobAccepted.drop 41).take 45 =
    FixedArrayCapacity.localProgram 55 1 62 ++ (jobAccepted.drop 59).take 27 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem jobAppendCapacity_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : JobSaved) (paramsLength : params.length = 8)
    (leftPointer rightPointer : UInt64) (left right : Array UInt64)
    (target counter padding60 padding61 oldNeed previous current capacity next result : UInt64)
    (remaining pageLimit : Nat)
    (leftAt : UInt64Array.At initial leftPointer left) (rightAt : UInt64Array.At initial rightPointer right)
    (leftProtected : heap.Protects leftPointer.toNat (leftPointer.toNat + 8 * (left.size + 1)))
    (rightProtected : heap.Protects rightPointer.toNat (rightPointer.toNat + 8 * (right.size + 1)))
    (valid : heap.At initial) (bound : left.size + right.size ≤ 56)
    (budget : OutputBudget initial heap (48 + 8 * (left.size + right.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (left.size + right.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final → (heap.allocate need).OwnsWords final node (left ++ right) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (jobAppendFrame params saved leftPointer rightPointer left.size right.size node.root right.size.toUInt64 padding60 padding61
          need previous current capacity next node.root) env) :
    wp Project.Beck.«module» ((jobAccepted.drop 41).take 45 ++ rest) Q initial
      (jobAppendFrame params saved leftPointer rightPointer left.size right.size target counter padding60 padding61
        oldNeed previous current capacity next result) env := by
  rw [job_append_capacity_shape, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 55 (left.size + right.size).toUInt64 1 62 Project.Beck.«module» env initial _
  · simp only [jobAppendFrame, jobPrefix, Locals.get, paramsLength, List.cons_append, List.nil_append,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  · rfl
  · simp [jobAppendFrame, paramsLength]
  · simp [Locals.validIndex, jobAppendFrame, jobPrefix, paramsLength]
  · rw [words_capacity (left.size + right.size) bound]
    have execute := jobAppendAllocated_owned env initial heap params saved paramsLength leftPointer rightPointer left right
      target counter padding60 padding61 previous current capacity next result remaining pageLimit
      leftAt rightAt leftProtected rightProtected valid bound budget Q rest finish
    simpa only [FixedArrayCapacity.capacityFrame, jobAppendFrame, jobPrefix, paramsLength,
      List.cons_append, List.nil_append, Locals.set, List.set, List.length, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      reduceIte] using execute

#print axioms jobAppendCapacity_owned

end Project.Beck.Execution
