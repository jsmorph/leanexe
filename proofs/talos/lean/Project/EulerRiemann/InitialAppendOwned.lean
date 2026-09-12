import Project.EulerRiemann.InitialAppendData
import Project.EulerRiemann.HeapGridFinish

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayFold FixedArrayCopy

theorem initial_append_owned_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (source upper : FreeNode) (need : UInt64) (left right : Array Traversal.Cell)
    (hHeap : heap.At initial) (hLeftOwner : heap.Owns initial source left)
    (hRightOwner : heap.Owns initial upper right)
    (hNeed : 8 * (7 * (left.size + right.size) + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hCounter : (resultFrame frame 55 (allocatedRoot heap.top need heap.nodes)).validIndex 56)
    (hSource : frame.get 48 = some (.i64 source.root))
    (hUpper : frame.get 49 = some (.i64 upper.root))
    (hTarget : frame.get 64 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (hLength : frame.get 52 = some (.i64 (UInt64.ofNat (left.size + right.size))))
    (hLeftCount : frame.get 53 = some (.i64 (UInt64.ofNat (7 * left.size))))
    (hRightCount : frame.get 54 = some (.i64 (UInt64.ofNat (7 * right.size))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source left →
      (heap.allocate need).Owns final upper right →
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes) (left ++ right) →
      Memory.WritesGrid (heap.allocateStore initial need) final
        (allocatedRoot heap.top need heap.nodes) (left.size + right.size) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final
        (counterFrame (resultFrame frame 55 (allocatedRoot heap.top need heap.nodes))
          56 (7 * right.size) hCounter) env) :
    wp module (initialGrowBody.drop 119 ++ rest) Q (heap.allocateStore initial need) frame env := by
  let target := allocatedRoot heap.top need heap.nodes
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => Nat.le_of_lt (hBump hNone)
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hFit
  have hCapacity := allocated_capacity need heap.nodes
  have hTarget32 : target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ 4294967296 := by
    change 48 ≤ target.toNat ∧ target.toNat + _ ≤ 4294967296 ∧ _ at hBounds
    omega
  have hTargetFit : target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤
      (heap.allocateStore initial need).mem.pages * 65536 := by
    change 48 ≤ target.toNat ∧ _ ∧ target.toNat + _ ≤
      (heap.allocateStore initial need).mem.pages * 65536 at hBounds
    omega
  have hSeparate (node : FreeNode) (grid : Array Traversal.Cell)
      (hOwner : heap.Owns initial node grid) :
      node.root.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
        target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ node.root.toNat := by
    have hDisjoint := allocated_region_disjoint heap.top need node heap.nodes
      hOwner.buffer.rootBound hOwner.separated hOwner.below hFit
    have hSourceCapacity := hOwner.buffer.capacity
    simp only [allocatedNode, regionsDisjoint, FreeNode.region] at hDisjoint
    dsimp only [target]
    omega
  apply initial_append_data_spec env _ frame source.root upper.root target left right
    hParams hLocals hValues hCounter hSource hUpper hTarget hLength hLeftCount hRightCount
    (hLeftOwner.allocated need hHeap hFit).buffer.values
    (hRightOwner.allocated need hHeap hFit).buffer.values hTarget32 hTargetFit
    (hSeparate source left hLeftOwner) (hSeparate upper right hRightOwner) Q rest
  intro final hWrites _ _ hResult
  have hFinished := heap.finishGrid initial final need (left ++ right) hHeap
    (by simpa only [Array.size_append] using hNeed) hBump
    (by simpa only [Array.size_append] using hWrites) hResult
  exact hNext final hFinished.1
    (hLeftOwner.swept need (left.size + right.size) hHeap hNeed hFit hWrites)
    (hRightOwner.swept need (left.size + right.size) hHeap hNeed hFit hWrites)
    hFinished.2 hWrites

#print axioms initial_append_owned_spec

end Project.EulerRiemann.Execution
