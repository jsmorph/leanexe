import Project.Beck.ExecutionBudget
import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

theorem pairStore_writes (initial : Store Unit) (root first second : UInt64)
    (bound : root.toNat + 24 ≤ 4294967296) :
    Memory.WritesRange initial (FixedArrayResult.pairStore initial root first second) root.toNat (root.toNat + 24) := by
  have address0 : root.toUInt32.toNat = root.toNat := by
    simpa [UInt64Array.wordAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3) (word := 0) (by simpa using bound) (by decide))
  have address1 : (FixedArrayResult.payloadAddress root 0).toUInt32.toNat = root.toNat + 8 := by
    simpa [UInt64Array.wordAddress, FixedArrayResult.payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3) (word := 1) (by simpa using bound) (by decide))
  have address2 : (FixedArrayResult.payloadAddress root 1).toUInt32.toNat = root.toNat + 16 := by
    simpa [UInt64Array.wordAddress, FixedArrayResult.payloadAddress] using
      (UInt64Array.wordAddress_toNat (ptr := root) (words := 3) (word := 2) (by simpa using bound) (by decide))
  have header := Memory.WritesRange.write64 initial root.toUInt32 2 root.toNat (root.toNat + 24)
    (by rw [address0]) (by rw [address0]; omega)
  have left := Memory.WritesRange.write64 (FixedArrayResult.writeLength initial root 2)
    (FixedArrayResult.payloadAddress root 0).toUInt32 first root.toNat (root.toNat + 24)
    (by rw [address1]; omega) (by rw [address1]; omega)
  have right := Memory.WritesRange.write64 (FixedArrayResult.writePayload (FixedArrayResult.writeLength initial root 2) root 0 first)
    (FixedArrayResult.payloadAddress root 1).toUInt32 second root.toNat (root.toNat + 24)
    (by rw [address2]; omega) (by rw [address2])
  exact (header.trans left).trans right

def pairWords (heap : Heap) (initial : Store Unit) (first second : UInt64) : Store Unit :=
  FixedArrayResult.pairStore (heap.allocateArrayStore initial 24 1) (allocatedRoot heap.top 24 heap.nodes) first second

theorem pairWords_resources (heap : Heap) (initial : Store Unit) (first second : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (budget : OutputBudget initial heap (72 + remaining) pageLimit Project.Beck.«module») :
    let final := pairWords heap initial first second
    let node := allocatedNode heap.top 24 heap.nodes
    (heap.allocate 24).At final ∧ (heap.allocate 24).OwnsWords final node #[first, second] ∧
    heap.Frame initial (heap.allocate 24) final ∧ FreshFor heap node ∧
    OutputBudget final (heap.allocate 24) remaining pageLimit Project.Beck.«module» := by
  have space := budget.bump 24 (by change 72 ≤ 72 + remaining; omega)
  have bounds := allocated_bounds initial heap.top 24 heap.nodes valid.freeList (fun h => (space h).1.le)
  have capacity := allocated_capacity 24 heap.nodes
  have address : (allocatedRoot heap.top 24 heap.nodes).toNat + 24 ≤ 4294967296 := by
    change 24 ≤ (allocatedCapacity 24 heap.nodes).toNat at capacity
    omega
  have memory : (allocatedRoot heap.top 24 heap.nodes).toNat + 24 ≤
      (heap.allocateArrayStore initial 24 1).mem.pages * 65536 := by
    change _ ≤ (FixedArrayAllocate.allocated initial heap.top 24 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    change 24 ≤ (allocatedCapacity 24 heap.nodes).toNat at capacity
    omega
  have represented := FixedArrayResult.pairStore_at (heap.allocateArrayStore initial 24 1)
    (allocatedRoot heap.top 24 heap.nodes) first second address memory
  have writes := pairStore_writes (heap.allocateArrayStore initial 24 1) (allocatedRoot heap.top 24 heap.nodes) first second address
  obtain ⟨finalValid, owned⟩ := heap.finishWords initial (pairWords heap initial first second) 24 #[first, second]
    valid (by simp) (fun h => (space h).1) writes represented
  exact ⟨finalValid, owned, heap.frame_arrayWritten initial _ 24 1 2 valid (by decide) (fun h => (space h).1.le) writes,
    allocated_fresh heap heap initial initial (Heap.Frame.refl heap initial) 24 (fun h => (space h).1.le),
    budget.allocated 24 1 remaining (by change 72 + remaining ≤ 72 + remaining; omega) writes⟩

#print axioms pairStore_writes
#print axioms pairWords_resources

end Project.Beck.Execution
