import Project.EulerRiemann.InitialScratch
import Project.EulerRiemann.InitialHeapBounds

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_append_branch_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (n size : Nat) (source upper : FreeNode)
    (tracker output : UInt64) (done : Bool) (left right : Array Traversal.Cell)
    (hFrame : InitialFrameAt frame fuel n size source.root tracker output done)
    (hScratch : I64LocalRange frame 57 66) (hUpper : frame.get 50 = some (.i64 upper.root))
    (hHeap : heap.At store) (hLeftOwner : heap.Owns store source left)
    (hRightOwner : heap.Owns store upper right)
    (hCount : left.size + right.size ≤ 1048576)
    (hBelow : InitialFreeBelow (left.size + right.size) heap.nodes)
    (hFit32 : heap.top.toNat + 48 + initialBytes (left.size + right.size) < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top
      (normalizedCapacity (UInt64.ofNat (left.size + right.size)) 7) ≤ store.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let requested := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 7
      let result := allocatedNode heap.top requested heap.nodes
      ∀ final resultFrame,
      (heap.allocate requested).At final →
      (heap.allocate requested).Owns final source left →
      (heap.allocate requested).Owns final upper right →
      (heap.allocate requested).Owns final result (left ++ right) →
      Memory.WritesGrid (heap.allocateStore store requested) final (heap.top + 48) (left.size + right.size) →
      InitialFrameAt resultFrame fuel n size source.root tracker output done →
      InitialScratch resultFrame →
      resultFrame.get 37 = some (.i64 (UInt64.ofNat n)) →
      resultFrame.get 38 = some (.i64 (UInt64.ofNat size)) →
      resultFrame.get 55 = some (.i64 result.root) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final resultFrame env) :
    wp module (initialGrowBody.drop 54 ++ rest) Q store frame env := by
  have hParams : frame.params.length = 5 := by simp [hFrame.params]
  have hLocals := hFrame.locals
  have hSaved : (frame.locals.take 54).length = 54 := by simp [hLocals]
  have hTail : (frame.locals.drop 60).length = 1 := by simp [hLocals]
  obtain ⟨need, previous, current, capacity, next, result, hEq⟩ := hScratch.window 54
    (by omega) (by omega) (by omega) hFrame.values
  let canonical := FixedArraySearch.frame frame.params (frame.locals.take 54) (frame.locals.drop 60)
    need previous current capacity next result
  have hCanonical : InitialFrameAt canonical fuel n size source.root tracker output done := by
    dsimp only [canonical]
    rw [← hEq]
    exact hFrame
  have hCanonicalScratch : I64LocalRange canonical 57 66 := by
    dsimp only [canonical]
    rw [← hEq]
    exact hScratch
  have hCanonicalUpper : canonical.get 50 = some (.i64 upper.root) := by
    dsimp only [canonical]
    rw [← hEq]
    exact hUpper
  have hN : canonical.get 1 = some (.i64 (UInt64.ofNat n)) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  have hSize : canonical.get 2 = some (.i64 (UInt64.ofNat size)) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  have hSource : canonical.get 4 = some (.i64 source.root) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  rw [hEq]
  apply initial_append_program_spec env store heap frame.params (frame.locals.take 54) (frame.locals.drop 60)
    hParams hSaved hTail need previous current capacity next result (UInt64.ofNat n) (UInt64.ofNat size)
    source upper left right hHeap hLeftOwner hRightOwner hCount hBelow hFit32 hPages hCap
    hN hSize hSource hCanonicalUpper
  dsimp only
  intro previousAfter final hFinalHeap hSourceOwner hUpperOwner hResultOwner hWrites
  let requested := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 7
  have hAllocated := hCanonical.appendAllocated hParams hSaved heap.top requested previousAfter
    upper.root (UInt64.ofNat left.size) (UInt64.ofNat right.size) right.size
  have hAllocatedScratch := initial_append_allocated_scratch hCanonicalScratch hParams hSaved hTail
    (UInt64.ofNat n) (UInt64.ofNat size) source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) heap.top requested previousAfter right.size
  have hGets := initial_append_done_gets frame.params (frame.locals.take 54) (frame.locals.drop 60)
    hParams hSaved hTail (UInt64.ofNat n) (UInt64.ofNat size) source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) heap.top requested previousAfter right.size
  apply hNext final _ hFinalHeap hSourceOwner hUpperOwner hResultOwner hWrites
    hAllocated hAllocatedScratch hGets.1 hGets.2.1
  have hNone := initial_no_fit (left.size + right.size) hCount heap.nodes hBelow
  simpa only [allocatedNode, allocatedRoot, hNone] using hGets.2.2.2

#print axioms initial_append_branch_spec

end Project.EulerRiemann.Execution
