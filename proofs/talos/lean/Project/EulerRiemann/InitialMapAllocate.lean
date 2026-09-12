import Project.EulerRiemann.InitialHeapAllocation
import Project.EulerRiemann.InitialMapOwned

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime

def initialMapAllocationFrame (params saved tail : List Wasm.Value)
    (base need previous : UInt64) : Locals :=
  FixedArraySearch.frame params saved tail need previous 0 (base + 48 + need)
    ((base + 48 + need - 1) / 65536 + 1) (base + 48)

def initialMapAllocationReady (params saved tail : List Wasm.Value)
    (base need previous : UInt64) (hStart : params.length + saved.length = 54) : Locals :=
  initialMapReadyFrame (initialMapAllocationFrame params saved tail base need previous) (base + 48)
    (by simp only [Locals.validIndex, initialMapAllocationFrame, FixedArraySearch.frame,
          List.length_append, List.length_cons, List.length_nil]
        omega)

theorem initial_map_allocate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (hParams : params.length = 5)
    (hSaved : saved.length = 49) (hTail : tail.length = 6)
    (hStart : params.length + saved.length = 54)
    (need previous current capacity next result : UInt64)
    (n offset : Nat) (source : FreeNode) (grid : Array Traversal.Cell)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none)
    (hNeed : 8 * (7 * grid.size + 1) ≤ need.toNat)
    (hFit32 : heap.top.toNat + 48 + need.toNat < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top need ≤ store.memoryCap module 0)
    (hn : n ≤ 800)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + offset < 1048576)
    (hN : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 1 =
      some (.i64 (UInt64.ofNat n)))
    (hOffset : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 10 =
      some (.i64 (UInt64.ofNat offset)))
    (hSource : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 48 =
      some (.i64 source.root))
    (hCount : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 49 =
      some (.i64 (UInt64.ofNat grid.size)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previousAfter final resultFrame,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes)
        (initialMapOutput n offset grid) →
      Memory.WritesGrid (heap.allocateStore store need) final (heap.top + 48) grid.size →
      InitialMapFrameAt (initialMapAllocationReady params saved tail heap.top need previousAfter hStart)
        grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (InitialAllocationSite.map.allocationProgram ++ initialMapDataProgram ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply initial_allocation_heap_spec .map env store heap params saved tail hStart
    need previous current capacity next result hHeap hNone (Nat.le_of_lt hFit32) hPages hCap
  intro previousAfter _ _ hPreserved
  let frame := initialMapAllocationFrame params saved tail heap.top need previousAfter
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 61 := by
    simp [frame, initialMapAllocationFrame, FixedArraySearch.frame, hSaved, hTail]
  have hCounter : frame.validIndex 51 := by
    simp [Locals.validIndex, hFrameParams, hFrameLocals]
  have hTarget : frame.get 59 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved tail need previousAfter 0
      (heap.top + 48 + need) ((heap.top + 48 + need - 1) / 65536 + 1) (heap.top + 48) 5 (by decide)
    simpa only [frame, initialMapAllocationFrame, hParams, hSaved, Nat.reduceAdd, List.getElem?_cons_zero,
      List.getElem?_cons_succ, allocatedRoot, hNone] using hGet
  apply initial_map_owned_spec env store heap frame n offset source need grid hHeap hOwner hNeed
    (fun _ => hFit32) hFrameParams hFrameLocals rfl hCounter hn hSum
    ((hPreserved 1 (by decide)).trans hN) ((hPreserved 10 (by decide)).trans hOffset)
    ((hPreserved 48 (by decide)).trans hSource) ((hPreserved 49 (by decide)).trans hCount)
    hTarget Q rest
  intro final resultFrame hFinalHeap hSourceOwner hTargetOwner hWrites hFrame
  apply hNext previousAfter final resultFrame hFinalHeap hSourceOwner hTargetOwner
  · simpa only [allocatedRoot, hNone] using hWrites
  · simpa only [initialMapAllocationReady, allocatedRoot, hNone, frame] using hFrame

#print axioms initial_map_allocate_spec

end Project.EulerRiemann.Execution
