import Project.EulerRiemann.InitialAppendAllocate
import Project.EulerRiemann.InitialAppendPrepareFrame
import Project.EulerRiemann.InitialAllocationOrder

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

theorem initial_append_program_parts : initialGrowBody.drop 54 = initialAppendInputProgram ++
    InitialAllocationSite.append.capacityProgram ++ InitialAllocationSite.append.allocationProgram ++
      initialGrowBody.drop 119 := by
  have hInput : initialGrowBody.drop 54 = (initialGrowBody.drop 54).take 32 ++ initialGrowBody.drop 86 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using (List.take_append_drop 32 (initialGrowBody.drop 54)).symm
  have hCapacity : initialGrowBody.drop 86 = (initialGrowBody.drop 86).take 18 ++ initialGrowBody.drop 104 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using (List.take_append_drop 18 (initialGrowBody.drop 86)).symm
  have hAllocation : initialGrowBody.drop 104 =
      (initialGrowBody.drop 104).take 15 ++ initialGrowBody.drop 119 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using (List.take_append_drop 15 (initialGrowBody.drop 104)).symm
  rw [hInput, hCapacity, hAllocation]
  simp only [initialAppendInputProgram, InitialAllocationSite.capacityProgram,
    InitialAllocationSite.allocationProgram, List.append_assoc]

theorem initial_append_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (hParams : params.length = 5)
    (hSaved : saved.length = 54) (hTail : tail.length = 1)
    (need previous current capacity next result n size : UInt64)
    (source upper : FreeNode) (left right : Array Traversal.Cell)
    (hHeap : heap.At store) (hLeftOwner : heap.Owns store source left)
    (hRightOwner : heap.Owns store upper right)
    (hCount : left.size + right.size ≤ 1048576)
    (hBelow : InitialFreeBelow (left.size + right.size) heap.nodes)
    (hFit32 : heap.top.toNat + 48 + initialBytes (left.size + right.size) < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top
      (normalizedCapacity (UInt64.ofNat (left.size + right.size)) 7) ≤ store.memoryCap module 0)
    (hN : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 1 = some (.i64 n))
    (hSize : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 2 = some (.i64 size))
    (hSource : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 4 =
      some (.i64 source.root))
    (hUpper : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 50 =
      some (.i64 upper.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let requested := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 7
      ∀ previousAfter final,
      (heap.allocate requested).At final →
      (heap.allocate requested).Owns final source left →
      (heap.allocate requested).Owns final upper right →
      (heap.allocate requested).Owns final (allocatedNode heap.top requested heap.nodes) (left ++ right) →
      Memory.WritesGrid (heap.allocateStore store requested) final (heap.top + 48) (left.size + right.size) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final
        (initialAppendAllocationDone params (initialAppendInputSaved saved n size source.root upper.root
          (UInt64.ofNat left.size) (UInt64.ofNat right.size)) tail heap.top requested previousAfter right.size
          (by rw [initial_append_input_saved_length, hParams, hSaved])) env) :
    wp module (initialGrowBody.drop 54 ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  let frame := FixedArraySearch.frame params saved tail need previous current capacity next result
  let input := initialAppendInputFrame frame n size source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size)
  let prepared := initialAppendInputSaved saved n size source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size)
  let requested := normalizedCapacity (UInt64.ofNat (left.size + right.size)) 7
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 61 := by simp [frame, FixedArraySearch.frame, hSaved, hTail]
  have hInputLocals : input.locals.length = 61 := by
    simpa only [input, initialAppendInputFrame, initialAppendLengthFrame, initialAppendPointersFrame,
      initialAppendCountsFrame, FixedArrayFold.resultFrame_locals_length] using hFrameLocals
  have hGets := initial_append_input_gets frame n size source.root upper.root
    (UInt64.ofNat left.size) (UInt64.ofNat right.size) hFrameParams hFrameLocals
  have hWordSum : UInt64.ofNat left.size + UInt64.ofNat right.size = UInt64.ofNat (left.size + right.size) :=
    (UInt64.ofNat_add left.size right.size).symm
  have hLeftWord : UInt64.ofNat left.size * 7 = UInt64.ofNat (7 * left.size) := by
    rw [Nat.mul_comm]
    exact (UInt64.ofNat_mul left.size 7).symm
  have hRightWord : UInt64.ofNat right.size * 7 = UInt64.ofNat (7 * right.size) := by
    rw [Nat.mul_comm]
    exact (UInt64.ofNat_mul right.size 7).symm
  have hFrameEq := initial_append_capacity_frame_eq params saved tail need previous current capacity next result
    n size source.root upper.root (UInt64.ofNat left.size) (UInt64.ofNat right.size) hParams hSaved
  rw [hWordSum] at hFrameEq
  have hPreserved (index : Nat) (hNe : index ≠ 59) :
      (FixedArraySearch.frame params prepared tail requested previous current capacity next result).get index =
        input.get index := by
    rw [← hFrameEq]
    exact FixedArrayFold.resultFrame_get_ne input 59 index requested
      (by change frame.params.length ≤ 59; omega) hNe
  have hNat : (UInt64.ofNat (left.size + right.size)).toNat = left.size + right.size :=
    UInt64.toNat_ofNat_of_lt' (by change left.size + right.size < 18446744073709551616; omega)
  have hRequested : requested.toNat = initialBytes (left.size + right.size) := by
    simpa only [hNat, initialBytes] using initial_capacity_toNat (UInt64.ofNat (left.size + right.size))
      (by simpa only [hNat] using hCount)
  have hPrepared : prepared.length = 54 := by rw [initial_append_input_saved_length, hSaved]
  have hStart : params.length + prepared.length = 59 := by omega
  rw [initial_append_program_parts, List.append_assoc, List.append_assoc, List.append_assoc]
  apply initial_append_input_spec env store frame n size source.root upper.root left right
    hFrameParams hFrameLocals rfl hN hSize hSource hUpper hLeftOwner.buffer.values hRightOwner.buffer.values
  apply initial_capacity_spec .append env store input (UInt64.ofNat (left.size + right.size))
    hFrameParams hInputLocals rfl
    (by simpa only [InitialAllocationSite.lengthLocal, input, hWordSum] using hGets.2.2.1)
  dsimp only [InitialAllocationSite.capacityLocal]
  rw [hFrameEq, ← List.append_assoc]
  apply initial_append_allocate_spec env store heap params prepared tail hParams hPrepared hTail hStart
    requested previous current capacity next result source upper left right hHeap hLeftOwner hRightOwner
    (Option.map_eq_none_iff.mp ((takeFirstFitFrom_project 0 requested heap.nodes).trans
      (initialFreeBelow_none (left.size + right.size) hCount heap.nodes hBelow)))
    (by rw [hRequested]; simp only [initialBytes]; omega)
    (by simpa only [hRequested] using hFit32) hPages hCap
  · exact (hPreserved 48 (by decide)).trans hGets.1
  · exact (hPreserved 49 (by decide)).trans hGets.2.1
  · simpa only [hWordSum] using (hPreserved 52 (by decide)).trans hGets.2.2.1
  · simpa only [hLeftWord] using (hPreserved 53 (by decide)).trans hGets.2.2.2.1
  · simpa only [hRightWord] using (hPreserved 54 (by decide)).trans hGets.2.2.2.2
  · exact hNext

#print axioms initial_append_program_parts
#print axioms initial_append_program_spec

end Project.EulerRiemann.Execution
