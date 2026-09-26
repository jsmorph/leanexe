import Project.Drone.Program
import Project.EulerRiemann.ArrayAllocationMemory
import Project.EulerRiemann.HeapWordsFinishBase

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem array_allocation_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap Project.Drone.«module» 0)
    (hPages : store.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.Drone.«module» rest Q (heap.allocateArrayStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) env) :
    wp Project.Drone.«module» (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  apply FixedArrayAllocate.program_spec Project.Drone.«module» env store params saved tail start hStart
    heap.top need stride previous current capacity next result heap.allocations heap.nodes
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hBump hPages rfl
  intro previous current capacity next
  simpa only [Heap.allocateArrayStore, allocatedRoot_shared] using hNext previous current capacity next


theorem release_words_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (words : Array UInt64)
    (hHeap : heap.At initial) (hOwner : heap.OwnsWords initial node words) :
    TerminatesWith env Project.Drone.«module» 29 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) := by
  obtain ⟨hMagic, hRc, hCapacity, hKind, hStride, hMask⟩ := hOwner.buffer.fresh
  have hBounds := hOwner.buffer.values.1
  have hFits := hOwner.buffer.values.2.1
  have hCall := Project.Runtime.release_frees_fixed_array_zero_mask_full env
    Project.Drone.«module» 29 initial node.root (freeHead heap.nodes)
    heap.releases heap.frees words.size 1 (typeIdx := some 29) rfl (by decide)
    (by omega) (by decide) hOwner.buffer.rootBound (by omega) (by omega)
    hMagic hRc hKind hOwner.buffer.values.lengthRead hStride hMask
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
  apply hCall.mono
  rintro final values ⟨hValues, hMem, hGlobals, hStore⟩
  have hGlobals' : final.globals =
      { globals := ((initial.globals.globals.set 4 (.i64 (heap.releases + 1))).set 5
        (.i64 (heap.frees + 1))).set 1 (.i64 node.root) } := congrArg Globals.mk hGlobals
  have hFinal : final = heap.releaseStore initial node := by
    rw [hStore, hMem, hGlobals']
    rfl
  refine ⟨hValues, hFinal, ?_⟩
  rw [hFinal]
  exact heap.release_at initial node hHeap hOwner.buffer.rootBound
    hOwner.buffer.addressBound hOwner.buffer.memoryBound hCapacity hOwner.below hOwner.separated

#print axioms array_allocation_spec
#print axioms release_words_exact
end Project.Drone.Execution
