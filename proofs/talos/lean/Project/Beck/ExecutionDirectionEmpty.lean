import Project.Beck.ExecutionDirectionStart
import Project.ProofKit.FixedArraySearchWindow

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionEmptyProgram (destination target : Nat) : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 102 ++ FixedArrayAllocate.program 102 1 ++
    [.localGet 107, .localSet 98] ++ FixedArrayResult.lengthStoreProgram 98 0 ++
    FixedArrayResult.finishProgram 98 (destination + 9) (target + 9)

set_option maxRecDepth 4096 in
theorem direction_empty_shapes :
    (func30.drop 42).take 43 = directionEmptyProgram 17 19 ∧
    (func30.drop 85).take 43 = directionEmptyProgram 17 20 ∧
    (func30.drop 128).take 43 = directionEmptyProgram 18 21 ∧
    (func30.drop 171).take 43 = directionEmptyProgram 18 22 := ⟨rfl, rfl, rfl, rfl⟩

def directionEmptySaved (saved : List Value) (destination target : Nat) (root : UInt64) : List Value :=
  ((saved.set 89 (.i64 root)).set destination (.i64 root)).set target (.i64 root)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionEmpty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (paramsSize : params.length = 9) (savedSize : saved.length = 93)
    (tailSize : tail.length = 13) (need previous current capacity afterNode result : UInt64)
    (destination target : Nat) (destinationBound : destination < 93) (targetBound : target < 93)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (budget : OutputBudget initial heap (56 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : let final := emptyWords heap initial
      let node := allocatedNode heap.top 8 heap.nodes
      (heap.allocate 8).At final → (heap.allocate 8).OwnsWords final node #[] →
      heap.Frame initial (heap.allocate 8) final → FreshFor heap node →
      OutputBudget final (heap.allocate 8) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity afterNode,
      wp Project.Beck.«module» rest Q final
        (FixedArraySearch.frame params (directionEmptySaved saved destination target node.root) tail
          8 previous current capacity afterNode node.root) env) :
    wp Project.Beck.«module» (directionEmptyProgram destination target ++ rest) Q initial
      (FixedArraySearch.frame params saved tail need previous current capacity afterNode result) env := by
  have space := budget.bump 8 (by change 56 ≤ 56 + remaining; omega)
  have bounds := emptyWords_bounds heap initial valid (fun h => (space h).1.le)
  have memory : (allocatedRoot heap.top 8 heap.nodes).toUInt32.toNat + 8 ≤
      (heap.allocateArrayStore initial 8 1).mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    exact bounds.2
  obtain ⟨allocatedValid, owned⟩ := emptyWords_owned heap initial valid (fun h => (space h).1)
  have preserved := emptyWords_frame heap initial valid (fun h => (space h).1.le)
  have fresh := allocated_fresh heap heap initial initial (Heap.Frame.refl heap initial) 8 (fun h => (space h).1.le)
  have writes := Project.EulerRiemann.Memory.writeLength_frame (heap.allocateArrayStore initial 8 1)
    (allocatedRoot heap.top 8 heap.nodes) 0 bounds.1
  have finalBudget := budget.allocated 8 1 remaining (by change 56 + remaining ≤ 56 + remaining; omega) writes
  dsimp only at finish
  simp only [directionEmptyProgram, List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 0 1 102 Project.Beck.«module» env initial _ rfl
    (by simp [FixedArraySearch.frame, paramsSize]) (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize, tailSize])
  have capacityFrame : FixedArrayCapacity.capacityFrame
      (FixedArraySearch.frame params saved tail need previous current capacity afterNode result) 102
        (FixedArrayCapacity.normalizedCapacity 0 1) =
      FixedArraySearch.frame params saved tail 8 previous current capacity afterNode result := by
    simp [FixedArrayCapacity.capacityFrame, FixedArraySearch.frame, paramsSize, savedSize,
      FixedArrayCapacity.normalizedCapacity, FixedArrayCapacity.unnormalizedCapacity]
  rw [capacityFrame]
  apply allocation_exact env initial heap params saved tail 102 (by omega) 8 previous current capacity afterNode result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity afterNode
  simp only [List.cons_append, List.nil_append]
  wp_run [FixedArraySearch.frame, paramsSize, savedSize, tailSize, List.getElem?_append, List.length_append,
    List.set_append, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  change wp Project.Beck.«module» (FixedArrayResult.lengthStoreProgram 98 0 ++ _) Q _
    (FixedArraySearch.frame params (saved.set 89 (.i64 (allocatedRoot heap.top 8 heap.nodes))) tail
      8 previous current capacity afterNode (allocatedRoot heap.top 8 heap.nodes)) env
  refine FixedArrayResult.lengthStore_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) 0 98 rfl ?_ memory _ _ ?_
  · simp [Locals.get, FixedArraySearch.frame, paramsSize, savedSize, tailSize]
  apply FixedArrayResult.finishProgram_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) 98 (destination + 9) (target + 9) rfl
    (by simp [Locals.get, FixedArraySearch.frame, paramsSize, savedSize, tailSize])
    (by simp [FixedArraySearch.frame, paramsSize])
    (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize, tailSize]; omega)
    (by simp [FixedArraySearch.frame, paramsSize])
    (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize, tailSize]; omega)
  simpa [FixedArrayResult.finishFrame, FixedArraySearch.frame, paramsSize, savedSize,
    List.set_append, destinationBound, targetBound,
    directionEmptySaved, emptyWords, allocatedNode] using
    finish allocatedValid owned preserved fresh finalBudget previous current capacity afterNode

#print axioms directionEmpty_exact

end Project.Beck.Execution
