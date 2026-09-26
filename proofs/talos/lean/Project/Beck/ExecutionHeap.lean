import Project.Beck.ExecutionScalar
import Project.EulerRiemann.HeapWordsFinish
import Project.EulerRiemann.MemoryOwnership
import Project.EulerRiemann.HeapFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

theorem allocation_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params saved tail : List Value) (start : Nat) (atStart : params.length + saved.length = start)
    (need previous current capacity next result : UInt64) (valid : heap.At initial)
    (space : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages heap.top need ≤ initial.memoryCap Project.Beck.«module» 0)
    (pages : initial.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q (heap.allocateArrayStore initial need 1)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) env) :
    wp Project.Beck.«module» (FixedArrayAllocate.program start 1 ++ rest) Q initial
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  apply FixedArrayAllocate.program_spec Project.Beck.«module» env initial params saved tail start atStart
    heap.top need 1 previous current capacity next result heap.allocations heap.nodes
    (by simp [valid.globals, Heap.globals]) (by simp [valid.globals, Heap.globals])
    (by simp [valid.globals, Heap.globals]) valid.freeList space pages rfl
  intro previous current capacity next
  exact finish previous current capacity next

def emptyWords (heap : Heap) (initial : Store Unit) : Store Unit :=
  FixedArrayResult.writeLength (heap.allocateArrayStore initial 8 1) (allocatedRoot heap.top 8 heap.nodes) 0

theorem allocatedWrites_resources (heap : Heap) (initial final : Store Unit)
    (need : UInt64) (lower upper : Nat)
    (writes : Project.ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1)
      final lower upper)
    (space : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (pages : initial.mem.pages ≤ 65536) :
    final.mem.pages ≤ 65536 ∧
      final.memoryCap Project.Beck.«module» 0 = initial.memoryCap Project.Beck.«module» 0 := by
  constructor
  · rw [writes.2.1]
    exact heap.allocateArrayStore_pages_bound initial need 1 65536 pages space
  · rw [writes.1]
    exact heap.allocateArrayStore_memoryCap initial need 1 Project.Beck.«module» 0

theorem emptyWords_bounds (heap : Heap) (initial : Store Unit) (valid : heap.At initial)
    (space : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 ≤ 4294967296) :
    (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤ 4294967296 ∧
      (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤
        (heap.allocateArrayStore initial 8 1).mem.pages * 65536 := by
  have bounds := allocated_bounds initial heap.top 8 heap.nodes valid.freeList space
  have capacity := allocated_capacity 8 heap.nodes
  change 8 ≤ (allocatedCapacity 8 heap.nodes).toNat at capacity
  change (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤ 4294967296 ∧
    (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤
      (FixedArrayAllocate.allocated initial heap.top 8 1 heap.nodes).mem.pages * 65536
  rw [arrayAllocated_pages]
  exact ⟨by omega, by omega⟩

theorem emptyWords_owned (heap : Heap) (initial : Store Unit) (valid : heap.At initial)
    (space : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 < 4294967296) :
    (heap.allocate 8).At (emptyWords heap initial) ∧
      (heap.allocate 8).OwnsWords (emptyWords heap initial) (allocatedNode heap.top 8 heap.nodes) #[] := by
  have bounds := emptyWords_bounds heap initial valid (fun h => (space h).le)
  have words : UInt64Array.At (emptyWords heap initial) (allocatedRoot heap.top 8 heap.nodes) #[] := by
    refine ⟨by simpa using bounds.1, ?_, ?_, ?_⟩
    · simpa [emptyWords, FixedArrayResult.writeLength, Mem.write64_pages] using bounds.2
    · exact Project.ProofKit.Memory.read64_write64 ..
    · intro i hi
      simp at hi
  have writes := Project.EulerRiemann.Memory.writeLength_frame (heap.allocateArrayStore initial 8 1)
    (allocatedRoot heap.top 8 heap.nodes) 0 bounds.1
  exact heap.finishWords initial (emptyWords heap initial) 8 #[] valid (by decide) space writes words

theorem emptyWords_frame (heap : Heap) (initial : Store Unit) (valid : heap.At initial)
    (space : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 ≤ 4294967296) :
    heap.Frame initial (heap.allocate 8) (emptyWords heap initial) := by
  have bounds := emptyWords_bounds heap initial valid space
  exact heap.frame_arrayWritten initial (emptyWords heap initial) 8 1 0 valid (by decide) space
    (Project.EulerRiemann.Memory.writeLength_frame (heap.allocateArrayStore initial 8 1)
      (allocatedRoot heap.top 8 heap.nodes) 0 bounds.1)

#print axioms allocation_exact
#print axioms emptyWords_owned
#print axioms emptyWords_frame

end Project.Beck.Execution
