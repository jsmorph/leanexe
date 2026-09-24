import Project.EulerRiemann.FrozenInitialExtractBranch
import Project.EulerRiemann.FrozenInitialResources
import Project.EulerRiemann.FrozenInitialPrefix

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_extract_resources_spec (env : HostEnv Unit) (initial store : Store Unit)
    (initialHeap heap : Heap) (frame : Locals) (fuel : UInt64) (n size : Nat)
    (source : FreeNode) (tracker output : UInt64) (done completed : Bool)
    (grid : Array Traversal.Cell) (limit pageLimit : Nat)
    (hFrame : InitialFrameAt frame fuel n size source.root tracker output done)
    (hScratch : InitialScratch frame) (hState : RetryStoreAt initial initialHeap store heap)
    (hOwner : heap.Owns store source grid) (hPrefix : InitialPrefix n grid.size grid)
    (hSize : size ≤ grid.size) (hCount : size ≤ 1048576)
    (hBelow : InitialFreeBelow (min size grid.size) heap.nodes)
    (hReserve : heap.top.toNat + initialRemainingBytes grid.size fuel.toNat size ≤ limit)
    (hLimit : limit < 4294967296) (hCap : limit ≤ store.memoryCap module 0 * 65536)
    (hPhysical : store.mem.pages ≤ pageLimit) (hPhysicalLimit : limit ≤ pageLimit * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let need := normalizedCapacity (UInt64.ofNat size) 7
      let result := allocatedNode heap.top need heap.nodes
      ∀ final resultFrame,
      RetryStoreAt initial initialHeap final (heap.allocate need) →
      (heap.allocate need).Owns final result (grid.extract 0 size) →
      InitialPrefix n size (grid.extract 0 size) →
      final.mem.pages ≤ pageLimit → (heap.allocate need).top.toNat ≤ limit →
      (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
        regionsDisjoint saved.region result.region) →
      result.capacity.toNat = initialBytes size →
      InitialFrameAt resultFrame fuel n size source.root tracker result.root (completed || done) →
      wp module rest Q final resultFrame env) :
    wp module (initialExtractBranch completed ++ rest) Q store frame env := by
  let need := normalizedCapacity (UInt64.ofNat size) 7
  have hFree := initialFreeBelow_extract hBelow
  have hFits := initial_extract_allocation_fits heap.top.toNat grid.size fuel.toNat size limit hReserve
  have hFit : heap.top.toNat + 48 + initialBytes size < 4294967296 := by omega
  apply initial_extract_branch_spec env store heap frame fuel n size source tracker output done completed
    grid hFrame hScratch hState.heapState hOwner hSize hCount hFree hFit hState.pages
    (initial_allocation_cap store heap size hCount (hFits.trans hCap))
  dsimp only
  intro final resultFrame hHeap _ hResult hWrites hResultFrame
  have hFinal := hState.initialAllocated size hCount hFree hFit hHeap hWrites
  have hPages := initial_allocated_pages heap store final size pageLimit hCount hPhysical
    (hFits.trans hPhysicalLimit) hWrites
  have hTop : (heap.allocate need).top.toNat ≤ limit := by
    rw [initial_allocated_top heap size hCount hFree hFit.le]
    exact hFits
  have hNone : takeFirstFitFrom 0 need heap.nodes = none := initial_no_fit size hCount heap.nodes hFree
  have hCapacity : (allocatedNode heap.top need heap.nodes).capacity.toNat = initialBytes size := by
    change (allocatedCapacity need heap.nodes).toNat = _
    rw [allocatedCapacity, hNone]
    exact initial_requested_bytes size hCount
  apply hNext final resultFrame hFinal.1 hResult (hPrefix.extracted size hSize) hPages hTop hFinal.2 hCapacity
  dsimp only [need] at hNone
  simpa only [allocatedNode, allocatedRoot, hNone] using hResultFrame

#print axioms initial_extract_resources_spec

end Project.EulerRiemann.Frozen.Execution
