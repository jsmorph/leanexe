import Project.EulerRiemann.InitialHeapAllocation
import Project.EulerRiemann.InitialExtractOwned

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayFold FixedArrayCopy

def initialExtractAllocationFrame (params saved : List Wasm.Value)
    (base need previous : UInt64) : Locals :=
  FixedArraySearch.frame params saved [] need previous 0 (base + 48 + need)
    ((base + 48 + need - 1) / 65536 + 1) (base + 48)

def initialExtractAllocationDone (params saved : List Wasm.Value)
    (base need previous : UInt64) (size : Nat) (hStart : params.length + saved.length = 60) : Locals :=
  counterFrame (resultFrame (initialExtractAllocationFrame params saved base need previous)
    56 (base + 48)) 57 (7 * size)
    (by simp only [Locals.validIndex, resultFrame_params, resultFrame_locals_length,
          initialExtractAllocationFrame, FixedArraySearch.frame, List.length_append,
          List.length_cons, List.length_nil]
        omega)

theorem initial_extract_allocate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hSaved : saved.length = 55) (hStart : params.length + saved.length = 60)
    (need previous current capacity next result : UInt64)
    (source : FreeNode) (grid : Array Traversal.Cell) (size : Nat)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid) (hSize : size ≤ grid.size)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none)
    (hNeed : 8 * (7 * size + 1) ≤ need.toNat)
    (hFit32 : heap.top.toNat + 48 + need.toNat < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top need ≤ store.memoryCap module 0)
    (hSource : (FixedArraySearch.frame params saved [] need previous current capacity next result).get 48 =
      some (.i64 source.root))
    (hLength : (FixedArraySearch.frame params saved [] need previous current capacity next result).get 53 =
      some (.i64 (UInt64.ofNat size)))
    (hOffset : (FixedArraySearch.frame params saved [] need previous current capacity next result).get 54 =
      some (.i64 0))
    (hCount : (FixedArraySearch.frame params saved [] need previous current capacity next result).get 55 =
      some (.i64 (UInt64.ofNat (7 * size))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previousAfter final,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes) (grid.extract 0 size) →
      Memory.WritesGrid (heap.allocateStore store need) final (heap.top + 48) size →
      wp module rest Q final
        (initialExtractAllocationDone params saved heap.top need previousAfter size hStart) env) :
    wp module (InitialAllocationSite.extract.allocationProgram ++ initialExtractDataProgram ++ rest) Q store
      (FixedArraySearch.frame params saved [] need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply initial_allocation_heap_spec .extract env store heap params saved [] hStart
    need previous current capacity next result hHeap hNone (Nat.le_of_lt hFit32) hPages hCap
  intro previousAfter _ _ hPreserved
  let frame := initialExtractAllocationFrame params saved heap.top need previousAfter
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 61 := by
    simp [frame, initialExtractAllocationFrame, FixedArraySearch.frame, hSaved]
  have hCounter : (resultFrame frame 56 (allocatedRoot heap.top need heap.nodes)).validIndex 57 := by
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hFrameParams, hFrameLocals]
  have hTarget : frame.get 65 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved [] need previousAfter 0
      (heap.top + 48 + need) ((heap.top + 48 + need - 1) / 65536 + 1) (heap.top + 48) 5 (by decide)
    simpa only [frame, initialExtractAllocationFrame, hParams, hSaved, Nat.reduceAdd, List.getElem?_cons_zero,
      List.getElem?_cons_succ, allocatedRoot, hNone] using hGet
  apply initial_extract_owned_spec env store heap frame source need grid size hHeap hOwner hSize
    hNeed (fun _ => hFit32) hFrameParams hFrameLocals rfl hCounter
    ((hPreserved 48 (by decide)).trans hSource) hTarget
    ((hPreserved 53 (by decide)).trans hLength) ((hPreserved 54 (by decide)).trans hOffset)
    ((hPreserved 55 (by decide)).trans hCount) Q rest
  intro final hFinalHeap hSourceOwner hResultOwner hWrites
  simpa only [initialExtractAllocationDone, allocatedRoot, hNone, frame] using
    hNext previousAfter final hFinalHeap hSourceOwner hResultOwner
      (by simpa only [allocatedRoot, hNone] using hWrites)

#print axioms initial_extract_allocate_spec

end Project.EulerRiemann.Execution
