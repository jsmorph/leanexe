import Project.Beck.ExecutionMemberSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 2048 in
theorem membershipSet_capacity_shape : membershipSetBranch.drop 4 =
    FixedArrayCapacity.localProgram 33 1 40 ++ membershipSetAllocated := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem membershipSetCapacity_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Value) (saved : MemberSetSaved) (paramsLength : params.length = 7)
    (ptr : UInt64) (words : Array UInt64) (index : Nat)
    (target counter value padding38 padding39 oldNeed previous current capacity next result : UInt64)
    (remaining pageLimit : Nat)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ final,
      let need := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top need heap.nodes
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final node (words.set! index value) →
      heap.Frame initial (heap.allocate need) final →
      OutputBudget final (heap.allocate need) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (memberSetFrame params saved ptr index words.size node.root words.size.toUInt64 value padding38 padding39
          need previous current capacity next node.root [.i64 node.root]) env) :
    wp Project.Beck.«module» (membershipSetBranch.drop 4 ++ rest) Q initial
      (memberSetFrame params saved ptr index words.size target counter value padding38 padding39
        oldNeed previous current capacity next result) env := by
  rw [membershipSet_capacity_shape, List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 33 words.size.toUInt64 1 40 Project.Beck.«module» env initial _
  · simp only [memberSetFrame, memberSetPrefix, Locals.get, paramsLength, List.cons_append, List.nil_append,
      List.length, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, reduceIte]
  · rfl
  · simp [memberSetFrame, paramsLength]
  · simp [Locals.validIndex, memberSetFrame, memberSetPrefix, paramsLength]
  · rw [words_capacity words.size bound]
    have execute := membershipSetAllocated_owned env initial heap params saved paramsLength ptr words index
      target counter value padding38 padding39 previous current capacity next result remaining pageLimit
      represented protects valid bound inside budget Q rest finish
    simpa only [FixedArrayCapacity.capacityFrame, memberSetFrame, memberSetPrefix, paramsLength,
      List.cons_append, List.nil_append, Locals.set, List.set, List.length, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
      reduceIte] using execute

#print axioms membershipSetCapacity_owned

end Project.Beck.Execution
