import Project.EulerRiemann.InitialExtractAllocate
import Project.EulerRiemann.InitialExtractPrepareFrame
import Project.EulerRiemann.InitialAllocationOrder

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

def initialExtractProgram : Wasm.Program := initialExtractBody.take 70

theorem initial_extract_program_shape : initialExtractProgram = initialExtractInputProgram ++
    InitialAllocationSite.extract.capacityProgram ++ InitialAllocationSite.extract.allocationProgram ++
      initialExtractDataProgram := by
  change initialExtractBody.take (61 + 9) = _
  rw [List.take_add, List.take_add (i := 46) (j := 15), List.take_add (i := 28) (j := 18)]
  rfl

theorem initial_done_extract_program : initialDoneBody.take 70 = initialExtractProgram := by
  rfl

theorem initial_extract_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved : List Wasm.Value) (hParams : params.length = 5) (hSaved : saved.length = 55)
    (need previous current capacity next result : UInt64)
    (source : FreeNode) (size : Nat) (grid : Array Traversal.Cell)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid) (hSize : size ≤ grid.size)
    (hCount : size ≤ 1048576) (hBelow : InitialFreeBelow size heap.nodes)
    (hFit32 : heap.top.toNat + 48 + initialBytes size < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top (normalizedCapacity (UInt64.ofNat size) 7) ≤
      store.memoryCap module 0)
    (hSizeParam : (FixedArraySearch.frame params saved [] need previous current capacity next result).get 2 =
      some (.i64 (UInt64.ofNat size)))
    (hSource : (FixedArraySearch.frame params saved [] need previous current capacity next result).get 4 =
      some (.i64 source.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let requested := normalizedCapacity (UInt64.ofNat size) 7
      ∀ previousAfter final,
      (heap.allocate requested).At final →
      (heap.allocate requested).Owns final source grid →
      (heap.allocate requested).Owns final (allocatedNode heap.top requested heap.nodes) (grid.extract 0 size) →
      Memory.WritesGrid (heap.allocateStore store requested) final (heap.top + 48) size →
      wp module rest Q final
        (initialExtractAllocationDone params
          (initialExtractInputSaved saved source.root (UInt64.ofNat size) (UInt64.ofNat grid.size))
          heap.top requested previousAfter size
          (by rw [initial_extract_input_saved_length, hParams, hSaved])) env) :
    wp module (initialExtractProgram ++ rest) Q store
      (FixedArraySearch.frame params saved [] need previous current capacity next result) env := by
  let frame := FixedArraySearch.frame params saved [] need previous current capacity next result
  let input := initialExtractInputFrame frame source.root (UInt64.ofNat size) (UInt64.ofNat grid.size)
  let prepared := initialExtractInputSaved saved source.root (UInt64.ofNat size) (UInt64.ofNat grid.size)
  let requested := normalizedCapacity (UInt64.ofNat size) 7
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 61 := by simp [frame, FixedArraySearch.frame, hSaved]
  have hInputLocals : input.locals.length = 61 := by
    simpa only [input, initialExtractInputFrame, initialExtractCountsFrame, initialExtractLoadFrame,
      initialExtractPointersFrame, FixedArrayFold.resultFrame_locals_length] using hFrameLocals
  have hGets := initial_extract_input_gets frame source.root (UInt64.ofNat size) (UInt64.ofNat grid.size)
    hFrameParams hFrameLocals
  have hFrameEq := initial_extract_capacity_frame_eq params saved need previous current capacity next result
    source.root (UInt64.ofNat size) (UInt64.ofNat grid.size) hParams hSaved
  have hPreserved (index : Nat) (hNe : index ≠ 60) :
      (FixedArraySearch.frame params prepared [] requested previous current capacity next result).get index =
        input.get index := by
    rw [← hFrameEq]
    exact FixedArrayFold.resultFrame_get_ne input 60 index requested
      (by change frame.params.length ≤ 60; omega) hNe
  have hNat : (UInt64.ofNat size).toNat = size :=
    UInt64.toNat_ofNat_of_lt' (by change size < 18446744073709551616; omega)
  have hRequested : requested.toNat = initialBytes size := by
    simpa only [hNat, initialBytes] using
      initial_capacity_toNat (UInt64.ofNat size) (by simpa only [hNat] using hCount)
  have hWordCount : UInt64.ofNat size * 7 = UInt64.ofNat (7 * size) := by
    rw [Nat.mul_comm]
    exact (UInt64.ofNat_mul size 7).symm
  have hPrepared : prepared.length = 55 := by rw [initial_extract_input_saved_length, hSaved]
  have hStart : params.length + prepared.length = 60 := by omega
  rw [initial_extract_program_shape, List.append_assoc, List.append_assoc, List.append_assoc]
  apply initial_extract_input_spec env store frame source.root size grid hFrameParams hFrameLocals rfl
    hSource hSizeParam hOwner.buffer.values hSize
  apply initial_capacity_spec .extract env store input (UInt64.ofNat size)
    hFrameParams hInputLocals rfl
    (by simpa only [InitialAllocationSite.lengthLocal, input] using hGets.2.1)
  dsimp only [InitialAllocationSite.capacityLocal]
  rw [hFrameEq, ← List.append_assoc]
  apply initial_extract_allocate_spec env store heap params prepared hParams hPrepared hStart
    requested previous current capacity next result source grid size hHeap hOwner hSize
    (Option.map_eq_none_iff.mp ((takeFirstFitFrom_project 0 requested heap.nodes).trans
      (initialFreeBelow_none size hCount heap.nodes hBelow)))
    (by rw [hRequested]; simp only [initialBytes]; omega)
    (by simpa only [hRequested] using hFit32) hPages hCap
  · exact (hPreserved 48 (by decide)).trans hGets.1
  · exact (hPreserved 53 (by decide)).trans hGets.2.1
  · exact (hPreserved 54 (by decide)).trans hGets.2.2.1
  · simpa only [hWordCount] using (hPreserved 55 (by decide)).trans hGets.2.2.2
  · exact hNext

#print axioms initial_extract_program_shape
#print axioms initial_done_extract_program
#print axioms initial_extract_program_spec

end Project.EulerRiemann.Execution
