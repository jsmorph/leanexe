import Project.Beck.ExecutionJobAllocate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem job_replicate_capacity_shape : (jobEligible.drop 16).take 42 =
    FixedArrayCapacity.localProgram 51 1 57 ++ (jobEligible.drop 34).take 24 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem jobReplicateCapacity_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : JobSaved) (paramsLength : params.length = 8) (count : Nat)
    (target counter value padding55 padding56 oldNeed previous current capacity next result : UInt64) (after : JobAfter)
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : count ≤ 56)
    (budget : OutputBudget initial heap (48 + 8 * (count + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (count + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (Array.replicate count value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (jobReplicateFrame params saved count node.root count.toUInt64 value padding55 padding56 need
          previous current capacity next node.root after) env) :
    wp Project.Beck.«module» ((jobEligible.drop 16).take 42 ++ rest) Q initial
      (jobReplicateFrame params saved count target counter value padding55 padding56 oldNeed
        previous current capacity next result after) env := by
  rw [job_replicate_capacity_shape, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 51 count.toUInt64 1 57 Project.Beck.«module» env initial _
  · simp only [jobReplicateFrame, jobPrefix, Locals.get, paramsLength, List.cons_append, List.nil_append,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  · rfl
  · simp [jobReplicateFrame, paramsLength]
  · simp [Locals.validIndex, jobReplicateFrame, jobPrefix, paramsLength]
  · rw [words_capacity count bound]
    have execute := jobReplicateAllocated_owned env initial heap params saved paramsLength count
      target counter value padding55 padding56 previous current capacity next result after remaining pageLimit valid bound budget Q rest finish
    simpa only [FixedArrayCapacity.capacityFrame, jobReplicateFrame, jobPrefix, paramsLength,
      List.cons_append, List.nil_append, Locals.set, List.set, List.length, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      reduceIte] using execute

#print axioms jobReplicateCapacity_owned

end Project.Beck.Execution
