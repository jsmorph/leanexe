import Project.EulerRiemann.FrozenInitialScratch
import Project.EulerRiemann.FrozenInitialFinish

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity FixedArrayFold FixedArrayCopy

def initialExtractBranch (completed : Bool) : Wasm.Program :=
  if completed then initialDoneBody else initialExtractBody

theorem initial_extract_branch_shape (completed : Bool) :
    initialExtractBranch completed = initialExtractProgram ++ initialExtractReturnProgram completed := by
  cases completed <;> exact (List.take_append_drop 70 _).symm

theorem initial_extract_branch_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (fuel : UInt64) (n size : Nat) (source : FreeNode)
    (tracker output : UInt64) (done completed : Bool) (grid : Array Traversal.Cell)
    (hFrame : InitialFrameAt frame fuel n size source.root tracker output done)
    (hScratch : InitialScratch frame)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid) (hSize : size ≤ grid.size)
    (hCount : size ≤ 1048576) (hBelow : InitialFreeBelow size heap.nodes)
    (hFit32 : heap.top.toNat + 48 + initialBytes size < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top (normalizedCapacity (UInt64.ofNat size) 7) ≤
      store.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let requested := normalizedCapacity (UInt64.ofNat size) 7
      ∀ final resultFrame,
      (heap.allocate requested).At final →
      (heap.allocate requested).Owns final source grid →
      (heap.allocate requested).Owns final (allocatedNode heap.top requested heap.nodes) (grid.extract 0 size) →
      Memory.WritesGrid (heap.allocateStore store requested) final (heap.top + 48) size →
      InitialFrameAt resultFrame fuel n size source.root tracker (heap.top + 48) (completed || done) →
      wp module rest Q final resultFrame env) :
    wp module (initialExtractBranch completed ++ rest) Q store frame env := by
  have hParams : frame.params.length = 5 := by simp [hFrame.params]
  have hLocals := hFrame.locals
  have hSaved : (frame.locals.take 55).length = 55 := by simp [hFrame.locals]
  have hTail : frame.locals.drop 61 = [] := List.drop_eq_nil_of_le (by omega)
  obtain ⟨need, previous, current, capacity, next, result, hEq⟩ := hScratch.window 55
    (by omega) (by omega) (by omega) hFrame.values
  simp only [hTail] at hEq
  let canonical := FixedArraySearch.frame frame.params (frame.locals.take 55) []
    need previous current capacity next result
  have hCanonical : InitialFrameAt canonical fuel n size source.root tracker output done := by
    dsimp only [canonical]
    rw [← hEq]
    exact hFrame
  have hSizeParam : canonical.get 2 = some (.i64 (UInt64.ofNat size)) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  have hSource : canonical.get 4 = some (.i64 source.root) := by
    simp [canonical, FixedArraySearch.frame, Locals.get, hFrame.params]
  rw [initial_extract_branch_shape, List.append_assoc, hEq]
  apply initial_extract_program_spec env store heap frame.params (frame.locals.take 55)
    hParams hSaved need previous current capacity next result source size grid
    hHeap hOwner hSize hCount hBelow hFit32 hPages hCap hSizeParam hSource
  dsimp only
  intro previousAfter final hFinalHeap hSourceOwner hResultOwner hWrites
  let requested := normalizedCapacity (UInt64.ofNat size) 7
  let saved := initialExtractInputSaved (frame.locals.take 55) source.root
    (UInt64.ofNat size) (UInt64.ofNat grid.size)
  have hStart : frame.params.length + saved.length = 60 := by
    simp [saved, initial_extract_input_saved_length, hParams, hSaved]
  let allocated := initialExtractAllocationDone frame.params saved heap.top requested previousAfter size hStart
  have hAllocated : InitialFrameAt allocated fuel n size source.root tracker output done :=
    hCanonical.extractAllocated hParams hSaved heap.top requested previousAfter (UInt64.ofNat grid.size)
  have hAllocatedParams : allocated.params.length = 5 := by simp [hAllocated.params]
  have hRoot : allocated.get 56 = some (.i64 (heap.top + 48)) := by
    dsimp only [allocated, initialExtractAllocationDone]
    rw [counterFrame_get_ne _ _ _ _ _ (by decide)]
    apply resultFrame_get_result
    · simp [initialExtractAllocationFrame, FixedArraySearch.frame, hParams]
    · simp [Locals.validIndex, initialExtractAllocationFrame, FixedArraySearch.frame,
        saved, initial_extract_input_saved_length, hParams, hSaved]
  apply initial_extract_return_spec env final allocated (heap.top + 48) completed
    hAllocatedParams hAllocated.locals hAllocated.values hRoot
  exact hNext final (initialExtractReturnFrame allocated (heap.top + 48) completed)
    hFinalHeap hSourceOwner hResultOwner hWrites (hAllocated.extractReturn (heap.top + 48) completed)

#print axioms initial_extract_branch_shape
#print axioms initial_extract_branch_spec

end Project.EulerRiemann.Frozen.Execution
