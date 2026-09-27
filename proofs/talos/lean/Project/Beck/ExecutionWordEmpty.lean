import Project.Beck.ExecutionDirectionStart
import Project.ProofKit.FixedArraySearchWindow

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def wordEmptyProgram (base pointer destination target : Nat) : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 (base + 9) ++ FixedArrayAllocate.program (base + 9) 1 ++
    [.localGet (base + 14), .localSet (pointer + 9)] ++ FixedArrayResult.lengthStoreProgram (pointer + 9) 0 ++
    FixedArrayResult.finishProgram (pointer + 9) (destination + 9) (target + 9)

def wordEmptySaved (saved : List Value) (pointer destination target : Nat) (root : UInt64) : List Value :=
  ((saved.set pointer (.i64 root)).set destination (.i64 root)).set target (.i64 root)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem wordEmpty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (base pointer : Nat) (paramsSize : params.length = 9) (savedSize : saved.length = base)
    (pointerBound : pointer < base) (need previous current capacity afterNode result : UInt64)
    (destination target : Nat) (destinationBound : destination < base) (targetBound : target < base)
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
        (FixedArraySearch.frame params (wordEmptySaved saved pointer destination target node.root) tail
          8 previous current capacity afterNode node.root) env) :
    wp Project.Beck.«module» (wordEmptyProgram base pointer destination target ++ rest) Q initial
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
  simp only [wordEmptyProgram, List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 0 1 (base + 9) Project.Beck.«module» env initial _ rfl
    (by simp [FixedArraySearch.frame, paramsSize]) (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize]; omega)
  have capacityFrame : FixedArrayCapacity.capacityFrame
      (FixedArraySearch.frame params saved tail need previous current capacity afterNode result) (base + 9)
        (FixedArrayCapacity.normalizedCapacity 0 1) =
      FixedArraySearch.frame params saved tail 8 previous current capacity afterNode result := by
    simp [FixedArrayCapacity.capacityFrame, FixedArraySearch.frame, paramsSize, savedSize, pointerBound,
      FixedArrayCapacity.normalizedCapacity, FixedArrayCapacity.unnormalizedCapacity]
  rw [capacityFrame]
  apply allocation_exact env initial heap params saved tail (base + 9) (by omega) 8 previous current capacity afterNode result valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity afterNode
  simp only [List.cons_append, List.nil_append]
  simp (discharger := omega) [wp_localGet_cons, wp_localSet_cons, Locals.get, Locals.set?,
    show base + 14 - 9 = base + 5 by omega, show base + 5 - base = 5 by omega, Nat.add_sub_cancel,
    FixedArraySearch.frame, paramsSize, savedSize, pointerBound, List.getElem?_append, List.length_append,
    List.set_append, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, List.take, List.drop, List.append_nil]
  simp only [show ¬base + 14 < 9 by omega,
    show base + 14 < 9 + (base + (tail.length + 1 + 1 + 1 + 1 + 1 + 1)) by omega,
    show pointer + 9 < 9 + (base + (tail.length + 1 + 1 + 1 + 1 + 1 + 1)) by omega, reduceIte]
  change wp Project.Beck.«module» (FixedArrayResult.lengthStoreProgram (pointer + 9) 0 ++ _) Q _
    (FixedArraySearch.frame params (saved.set pointer (.i64 (allocatedRoot heap.top 8 heap.nodes))) tail
      8 previous current capacity afterNode (allocatedRoot heap.top 8 heap.nodes)) env
  refine FixedArrayResult.lengthStore_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) 0 (pointer + 9) rfl ?_ memory _ _ ?_
  · simp [Locals.get, FixedArraySearch.frame, paramsSize, savedSize, pointerBound, List.getElem?_append,
      show pointer + 9 < 9 + (base + (tail.length + 1 + 1 + 1 + 1 + 1 + 1)) by omega]
  apply FixedArrayResult.finishProgram_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) (pointer + 9) (destination + 9) (target + 9) rfl
    (by simp [Locals.get, FixedArraySearch.frame, paramsSize, savedSize, pointerBound, List.getElem?_append,
      show pointer + 9 < 9 + (base + (tail.length + 1 + 1 + 1 + 1 + 1 + 1)) by omega])
    (by simp [FixedArraySearch.frame, paramsSize])
    (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize, pointerBound]; omega)
    (by simp [FixedArraySearch.frame, paramsSize])
    (by simp [Locals.validIndex, FixedArraySearch.frame, paramsSize, savedSize, pointerBound]; omega)
  simpa [FixedArrayResult.finishFrame, FixedArraySearch.frame, paramsSize, savedSize, pointerBound,
    List.set_append, destinationBound, targetBound,
    wordEmptySaved, emptyWords, allocatedNode] using
    finish allocatedValid owned preserved fresh finalBudget previous current capacity afterNode

#print axioms wordEmpty_exact

end Project.Beck.Execution
