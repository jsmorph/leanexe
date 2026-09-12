import Project.EulerRiemann.InitialHeapAllocation
import Project.EulerRiemann.InitialAppendOwned

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayFold FixedArrayCopy

def initialAppendAllocationFrame (params saved tail : List Wasm.Value)
    (base need previous : UInt64) : Locals :=
  FixedArraySearch.frame params saved tail need previous 0 (base + 48 + need)
    ((base + 48 + need - 1) / 65536 + 1) (base + 48)

def initialAppendAllocationDone (params saved tail : List Wasm.Value)
    (base need previous : UInt64) (count : Nat) (hStart : params.length + saved.length = 59) : Locals :=
  counterFrame (resultFrame (initialAppendAllocationFrame params saved tail base need previous)
    55 (base + 48)) 56 (7 * count)
    (by simp only [Locals.validIndex, resultFrame_params, resultFrame_locals_length,
          initialAppendAllocationFrame, FixedArraySearch.frame, List.length_append,
          List.length_cons, List.length_nil]
        omega)

theorem initial_append_allocate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (hParams : params.length = 5)
    (hSaved : saved.length = 54) (hTail : tail.length = 1)
    (hStart : params.length + saved.length = 59)
    (need previous current capacity next result : UInt64)
    (source upper : FreeNode) (left right : Array Traversal.Cell)
    (hHeap : heap.At store) (hLeftOwner : heap.Owns store source left)
    (hRightOwner : heap.Owns store upper right)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none)
    (hNeed : 8 * (7 * (left.size + right.size) + 1) ≤ need.toNat)
    (hFit32 : heap.top.toNat + 48 + need.toNat < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top need ≤ store.memoryCap module 0)
    (hSource : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 48 =
      some (.i64 source.root))
    (hUpper : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 49 =
      some (.i64 upper.root))
    (hLength : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 52 =
      some (.i64 (UInt64.ofNat (left.size + right.size))))
    (hLeftCount : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 53 =
      some (.i64 (UInt64.ofNat (7 * left.size))))
    (hRightCount : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 54 =
      some (.i64 (UInt64.ofNat (7 * right.size))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previousAfter final,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source left →
      (heap.allocate need).Owns final upper right →
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes) (left ++ right) →
      Memory.WritesGrid (heap.allocateStore store need) final (heap.top + 48) (left.size + right.size) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final
        (initialAppendAllocationDone params saved tail heap.top need previousAfter right.size hStart) env) :
    wp module (InitialAllocationSite.append.allocationProgram ++ initialGrowBody.drop 119 ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply initial_allocation_heap_spec .append env store heap params saved tail hStart
    need previous current capacity next result hHeap hNone (Nat.le_of_lt hFit32) hPages hCap
  intro previousAfter _ _ hPreserved
  let frame := initialAppendAllocationFrame params saved tail heap.top need previousAfter
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 61 := by
    simp [frame, initialAppendAllocationFrame, FixedArraySearch.frame, hSaved, hTail]
  have hCounter : (resultFrame frame 55 (allocatedRoot heap.top need heap.nodes)).validIndex 56 := by
    simp [Locals.validIndex, resultFrame_params, resultFrame_locals_length, hFrameParams, hFrameLocals]
  have hTarget : frame.get 64 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved tail need previousAfter 0
      (heap.top + 48 + need) ((heap.top + 48 + need - 1) / 65536 + 1) (heap.top + 48) 5 (by decide)
    simpa only [frame, initialAppendAllocationFrame, hParams, hSaved, Nat.reduceAdd, List.getElem?_cons_zero,
      List.getElem?_cons_succ, allocatedRoot, hNone] using hGet
  apply initial_append_owned_spec env store heap frame source upper need left right hHeap hLeftOwner
    hRightOwner hNeed (fun _ => hFit32) hFrameParams hFrameLocals rfl hCounter
    ((hPreserved 48 (by decide)).trans hSource) ((hPreserved 49 (by decide)).trans hUpper)
    hTarget ((hPreserved 52 (by decide)).trans hLength)
    ((hPreserved 53 (by decide)).trans hLeftCount) ((hPreserved 54 (by decide)).trans hRightCount) Q rest
  intro final hFinalHeap hSourceOwner hUpperOwner hResultOwner hWrites
  simpa only [initialAppendAllocationDone, allocatedRoot, hNone, frame] using
    hNext previousAfter final hFinalHeap hSourceOwner hUpperOwner hResultOwner
      (by simpa only [allocatedRoot, hNone] using hWrites)

#print axioms initial_append_allocate_spec

end Project.EulerRiemann.Execution
