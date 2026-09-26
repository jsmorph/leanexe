import Project.EulerRiemann.FrozenInitialScratch
import Project.EulerRiemann.FrozenInitialHeapBounds

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_map_branch_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (n size : Nat) (source : FreeNode)
    (tracker output : UInt64) (done : Bool) (grid : Array Traversal.Cell)
    (hFrame : InitialFrameAt frame fuel n size source.root tracker output done)
    (hScratch : InitialScratch frame)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (hCount : grid.size ≤ 1048576) (hBelow : InitialFreeBelow grid.size heap.nodes)
    (hFit32 : heap.top.toNat + 48 + initialBytes grid.size < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
      store.memoryCap module 0)
    (hn : n ≤ 800)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + grid.size < 1048576)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let requested := normalizedCapacity (UInt64.ofNat grid.size) 7
      let upper := allocatedNode heap.top requested heap.nodes
      ∀ final resultFrame,
      (heap.allocate requested).At final →
      (heap.allocate requested).Owns final source grid →
      (heap.allocate requested).Owns final upper (initialMapOutput n grid.size grid) →
      Memory.WritesGrid (heap.allocateStore store requested) final (heap.top + 48) grid.size →
      InitialFrameAt resultFrame fuel n size source.root tracker output done →
      I64LocalRange resultFrame 57 66 → resultFrame.get 50 = some (.i64 upper.root) →
      wp module rest Q final resultFrame env) :
    wp module (initialMapProgram ++ rest) Q store frame env := by
  have hParams : frame.params.length = 5 := by simp [hFrame.params]
  have hLocals := hFrame.locals
  have hSaved : (frame.locals.take 49).length = 49 := by simp [hLocals]
  have hTail : (frame.locals.drop 55).length = 6 := by simp [hLocals]
  obtain ⟨need, previous, current, capacity, next, result, hEq⟩ := hScratch.window 49
    (by omega) (by omega) (by omega) hFrame.values
  let canonical := FixedArraySearch.frame frame.params (frame.locals.take 49) (frame.locals.drop 55)
    need previous current capacity next result
  have hCanonical : InitialFrameAt canonical fuel n size source.root tracker output done := by
    dsimp only [canonical]
    rw [← hEq]
    exact hFrame
  have hCanonicalScratch : InitialScratch canonical := by
    dsimp only [canonical]
    rw [← hEq]
    exact hScratch
  have hN : canonical.get 1 = some (.i64 (UInt64.ofNat n)) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  have hSource : canonical.get 4 = some (.i64 source.root) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  rw [hEq]
  apply initial_map_program_spec env store heap frame.params (frame.locals.take 49) (frame.locals.drop 55)
    hParams hSaved hTail need previous current capacity next result n source grid
    hHeap hOwner hCount hBelow hFit32 hPages hCap hn hSum hN hSource
  dsimp only
  intro previousAfter final resultFrame hFinalHeap hSourceOwner hUpperOwner hWrites hMapped
  let requested := normalizedCapacity (UInt64.ofNat grid.size) 7
  have hReady := hCanonical.mapAllocated hParams hSaved heap.top requested previousAfter (UInt64.ofNat grid.size)
  have hReadyScratch := hCanonicalScratch.mapAllocated hParams hSaved hTail
    source.root (UInt64.ofNat grid.size) heap.top requested previousAfter
  have hTarget : resultFrame.get 50 = some (.i64 (heap.top + 48)) := by
    rw [hMapped.preserved 50 (by decide) (by decide) (by decide)]
    exact initial_map_ready_target _ _ _ hParams
  have hNone := initial_no_fit grid.size hCount heap.nodes hBelow
  apply hNext final resultFrame hFinalHeap hSourceOwner hUpperOwner hWrites
    (hReady.mapped hMapped) (hMapped.scratchTail hReadyScratch)
  simpa only [allocatedNode, allocatedRoot, hNone] using hTarget

#print axioms initial_map_branch_spec

end Project.EulerRiemann.Frozen.Execution
