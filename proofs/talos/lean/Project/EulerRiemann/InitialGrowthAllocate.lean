import Project.EulerRiemann.InitialMapBranch
import Project.EulerRiemann.InitialAppendBranch
import Project.EulerRiemann.InitialResources

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

def initialGrowthHeap (heap : Heap) (count : Nat) : Heap :=
  (heap.allocate (normalizedCapacity (UInt64.ofNat count) 7)).allocate
    (normalizedCapacity (UInt64.ofNat (count + count)) 7)

def initialGrowthNode (heap : Heap) (count : Nat) : FreeNode :=
  let mapped := heap.allocate (normalizedCapacity (UInt64.ofNat count) 7)
  allocatedNode mapped.top (normalizedCapacity (UInt64.ofNat (count + count)) 7) mapped.nodes

theorem initial_growth_allocate_spec (env : HostEnv Unit) (initial store : Store Unit)
    (initialHeap heap : Heap) (frame : Locals) (fuel : UInt64) (n size : Nat)
    (source : FreeNode) (tracker output : UInt64) (done : Bool) (grid : Array Traversal.Cell)
    (limit pageLimit : Nat)
    (hFrame : InitialFrameAt frame fuel n size source.root tracker output done)
    (hScratch : InitialScratch frame) (hState : RetryStoreAt initial initialHeap store heap)
    (hOwner : heap.Owns store source grid)
    (hCount : grid.size + grid.size ≤ 1048576)
    (hBelow : InitialFreeBelow (min size grid.size) heap.nodes)
    (hFuel : 0 < fuel.toNat)
    (hReserve : heap.top.toNat + initialRemainingBytes grid.size fuel.toNat size ≤ limit)
    (hLimit : limit < 4294967296)
    (hCap : limit ≤ store.memoryCap module 0 * 65536)
    (hPhysical : store.mem.pages ≤ pageLimit) (hPhysicalLimit : limit ≤ pageLimit * 65536)
    (hn : n ≤ 800)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + grid.size < 1048576)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      RetryStoreAt initial initialHeap final (initialGrowthHeap heap grid.size) →
      (initialGrowthHeap heap grid.size).Owns final source grid →
      (initialGrowthHeap heap grid.size).Owns final (initialGrowthNode heap grid.size)
        (grid ++ initialMapOutput n grid.size grid) →
      final.mem.pages ≤ pageLimit →
      (initialGrowthHeap heap grid.size).nodes = heap.nodes →
      (initialGrowthHeap heap grid.size).top.toNat +
        initialRemainingBytes (grid.size + grid.size) (fuel.toNat - 1) size ≤ limit →
      regionsDisjoint source.region (initialGrowthNode heap grid.size).region →
      (∀ (saved : FreeNode) (savedGrid : Array Traversal.Cell), initialHeap.Owns initial saved savedGrid →
        regionsDisjoint saved.region (initialGrowthNode heap grid.size).region) →
      (initialGrowthNode heap grid.size).capacity.toNat = initialBytes (grid.size + grid.size) →
      InitialFrameAt resultFrame fuel n size source.root tracker output done →
      InitialScratch resultFrame →
      resultFrame.get 37 = some (.i64 (UInt64.ofNat n)) →
      resultFrame.get 38 = some (.i64 (UInt64.ofNat size)) →
      resultFrame.get 55 = some (.i64 (initialGrowthNode heap grid.size).root) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final resultFrame env) :
    wp module (initialGrowBody ++ rest) Q store frame env := by
  let mapNeed := normalizedCapacity (UInt64.ofNat grid.size) 7
  let appendNeed := normalizedCapacity (UInt64.ofNat (grid.size + grid.size)) 7
  let mapHeap := heap.allocate mapNeed
  have hMapCount : grid.size ≤ 1048576 := by omega
  have hMapBelow := initialFreeBelow_map hBelow
  have hAppendBelow := initialFreeBelow_append hBelow
  have hFits := initial_growth_allocations_fit heap.top.toNat grid.size fuel.toNat size limit
    hCount hFuel hReserve
  have hMapFit : heap.top.toNat + 48 + initialBytes grid.size < 4294967296 := by omega
  have hMapTop : mapHeap.top.toNat = heap.top.toNat + 48 + initialBytes grid.size :=
    initial_allocated_top heap grid.size hMapCount hMapBelow hMapFit.le
  have hMapNodes : mapHeap.nodes = heap.nodes := initial_allocated_nodes heap grid.size hMapCount hMapBelow
  have hAppendFit : mapHeap.top.toNat + 48 + initialBytes (grid.size + grid.size) < 4294967296 := by
    rw [hMapTop]
    omega
  have hAppendBelowMap : InitialFreeBelow (grid.size + grid.size) mapHeap.nodes := by
    rw [hMapNodes]
    exact hAppendBelow
  have hUpperSize : (initialMapOutput n grid.size grid).size = grid.size := by
    simp [initialMapOutput]
  have hProgram : initialGrowBody = initialMapProgram ++ initialGrowBody.drop 54 :=
    (List.take_append_drop 54 initialGrowBody).symm
  rw [hProgram, List.append_assoc]
  apply initial_map_branch_spec env store heap frame fuel n size source tracker output done grid
    hFrame hScratch hState.heapState hOwner hMapCount hMapBelow hMapFit hState.pages
    (initial_allocation_cap store heap grid.size hMapCount (hFits.1.trans hCap)) hn hSum
  dsimp only
  intro mapped mappedFrame hMappedHeap hMappedSource hUpperOwner hMapWrites hMappedFrame hMappedScratch hUpper
  have hMapState := hState.initialAllocated grid.size hMapCount hMapBelow hMapFit hMappedHeap hMapWrites
  have hMapPhysical : mapped.mem.pages ≤ pageLimit :=
    initial_allocated_pages heap store mapped grid.size pageLimit hMapCount hPhysical
      (hFits.1.trans hPhysicalLimit) hMapWrites
  have hMapCap : mapped.memoryCap module 0 = store.memoryCap module 0 :=
    hMapState.1.cap.trans hState.cap.symm
  have hAppendCap := initial_allocation_cap mapped mapHeap (grid.size + grid.size) hCount
    (by rw [hMapTop, hMapCap]; omega)
  apply initial_append_branch_spec env mapped mapHeap mappedFrame fuel n size source
    (allocatedNode heap.top mapNeed heap.nodes) tracker output done grid (initialMapOutput n grid.size grid)
    hMappedFrame hMappedScratch hUpper hMappedHeap hMappedSource hUpperOwner
    (by simpa only [hUpperSize] using hCount) (by simpa only [hUpperSize] using hAppendBelowMap)
    (by simpa only [hUpperSize] using hAppendFit) hMapState.1.pages
    (by simpa only [hUpperSize] using hAppendCap)
  dsimp only
  intro final resultFrame hFinalHeap hFinalSource _ hResultOwner hAppendWrites hResultFrame hResultScratch hN hSize hRoot
  simp only [hUpperSize] at hFinalHeap hFinalSource hResultOwner hAppendWrites hRoot
  have hFinalState := hMapState.1.initialAllocated (grid.size + grid.size) hCount hAppendBelowMap
    hAppendFit hFinalHeap hAppendWrites
  have hFinalPhysical : final.mem.pages ≤ pageLimit :=
    initial_allocated_pages mapHeap mapped final (grid.size + grid.size) pageLimit hCount hMapPhysical
      (by rw [hMapTop]; omega) hAppendWrites
  have hFinalNodes : (initialGrowthHeap heap grid.size).nodes = heap.nodes :=
    (initial_allocated_nodes mapHeap (grid.size + grid.size) hCount hAppendBelowMap).trans hMapNodes
  have hFinalTop := initial_allocated_top mapHeap (grid.size + grid.size) hCount hAppendBelowMap hAppendFit.le
  have hFinalReserve : (initialGrowthHeap heap grid.size).top.toNat +
      initialRemainingBytes (grid.size + grid.size) (fuel.toNat - 1) size ≤ limit := by
    change (mapHeap.allocate appendNeed).top.toNat + _ ≤ _
    rw [hFinalTop, hMapTop]
    simpa only [Nat.add_assoc] using
      initial_growth_reserve_step heap.top.toNat grid.size fuel.toNat size limit hCount hFuel hReserve
  have hNeed : appendNeed.toNat = initialBytes (grid.size + grid.size) :=
    initial_requested_bytes (grid.size + grid.size) hCount
  have hBump : takeFirstFitFrom 0 appendNeed mapHeap.nodes = none →
      mapHeap.top.toNat + 48 + appendNeed.toNat ≤ 4294967296 := by
    intro _
    simpa only [hNeed] using hAppendFit.le
  have hSeparated := allocated_region_disjoint mapHeap.top appendNeed source mapHeap.nodes
    hMappedSource.buffer.rootBound hMappedSource.separated hMappedSource.below hBump
  have hNodeCapacity : (initialGrowthNode heap grid.size).capacity.toNat =
      initialBytes (grid.size + grid.size) := by
    have hNone := initial_no_fit (grid.size + grid.size) hCount mapHeap.nodes hAppendBelowMap
    change (allocatedCapacity appendNeed mapHeap.nodes).toNat = _
    rw [allocatedCapacity, hNone]
    exact hNeed
  exact hNext final resultFrame hFinalState.1 hFinalSource hResultOwner hFinalPhysical hFinalNodes
    hFinalReserve hSeparated hFinalState.2 hNodeCapacity hResultFrame hResultScratch hN hSize hRoot

#print axioms initial_growth_allocate_spec

end Project.EulerRiemann.Execution
