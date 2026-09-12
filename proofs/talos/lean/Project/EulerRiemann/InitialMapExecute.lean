import Project.EulerRiemann.InitialMapAllocate
import Project.EulerRiemann.InitialMapPrepareFrame
import Project.EulerRiemann.InitialAllocationOrder

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayCapacity

def initialMapProgram : Wasm.Program := initialGrowBody.take 54

theorem initial_map_program_shape : initialMapProgram = initialMapInputProgram ++
    InitialAllocationSite.map.capacityProgram ++ InitialAllocationSite.map.allocationProgram ++
      initialMapDataProgram := by
  change initialGrowBody.take (45 + 9) = _
  rw [List.take_add, List.take_add (i := 30) (j := 15), List.take_add (i := 12) (j := 18)]
  rfl

theorem initial_map_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (hParams : params.length = 5)
    (hSaved : saved.length = 49) (hTail : tail.length = 6)
    (need previous current capacity next result : UInt64)
    (n : Nat) (source : FreeNode) (grid : Array Traversal.Cell)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (hCount : grid.size ≤ 1048576) (hBelow : InitialFreeBelow grid.size heap.nodes)
    (hFit32 : heap.top.toNat + 48 + initialBytes grid.size < 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top (normalizedCapacity (UInt64.ofNat grid.size) 7) ≤
      store.memoryCap module 0)
    (hn : n ≤ 800)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + grid.size < 1048576)
    (hN : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 1 =
      some (.i64 (UInt64.ofNat n)))
    (hSource : (FixedArraySearch.frame params saved tail need previous current capacity next result).get 4 =
      some (.i64 source.root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let requested := normalizedCapacity (UInt64.ofNat grid.size) 7
      ∀ previousAfter final resultFrame,
      (heap.allocate requested).At final →
      (heap.allocate requested).Owns final source grid →
      (heap.allocate requested).Owns final (allocatedNode heap.top requested heap.nodes)
        (initialMapOutput n grid.size grid) →
      Memory.WritesGrid (heap.allocateStore store requested) final (heap.top + 48) grid.size →
      InitialMapFrameAt (initialMapAllocationReady params
        (initialMapInputSaved saved source.root (UInt64.ofNat grid.size)) tail heap.top requested
        previousAfter (by rw [initial_map_input_saved_length, hParams, hSaved]))
        grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (initialMapProgram ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  let frame := FixedArraySearch.frame params saved tail need previous current capacity next result
  let input := initialMapInputFrame frame source.root (UInt64.ofNat grid.size)
  let prepared := initialMapInputSaved saved source.root (UInt64.ofNat grid.size)
  let requested := normalizedCapacity (UInt64.ofNat grid.size) 7
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 61 := by
    simp [frame, FixedArraySearch.frame, hSaved, hTail]
  have hGets := initial_map_input_gets frame source.root (UInt64.ofNat grid.size)
    hFrameParams hFrameLocals
  have hPreserved (index : Nat) (hNe : index ≠ 54) :
      (FixedArraySearch.frame params prepared tail requested previous current capacity next result).get index =
        input.get index := by
    have hEq := initial_map_capacity_frame_eq params saved tail need previous current capacity next result
      source.root (UInt64.ofNat grid.size) hParams hSaved
    rw [← hEq]
    exact FixedArrayFold.resultFrame_get_ne input 54 index requested
      (by change frame.params.length ≤ 54; omega) hNe
  have hNat : (UInt64.ofNat grid.size).toNat = grid.size :=
    UInt64.toNat_ofNat_of_lt' (by change grid.size < 18446744073709551616; omega)
  have hRequested : requested.toNat = initialBytes grid.size := by
    simpa only [hNat, initialBytes] using
      initial_capacity_toNat (UInt64.ofNat grid.size) (by simpa only [hNat] using hCount)
  have hPrepared : prepared.length = 49 := by
    rw [initial_map_input_saved_length, hSaved]
  have hStart : params.length + prepared.length = 54 := by omega
  rw [initial_map_program_shape, List.append_assoc, List.append_assoc, List.append_assoc]
  apply initial_map_input_spec env store frame source.root grid hFrameParams hFrameLocals rfl
    hSource hOwner.buffer.values
  apply initial_capacity_spec .map env store input (UInt64.ofNat grid.size)
    hFrameParams (by simpa only [input, initial_map_input_locals] using hFrameLocals) rfl hGets.2.2
  dsimp only [input, frame, InitialAllocationSite.capacityLocal]
  rw [initial_map_capacity_frame_eq params saved tail need previous current capacity next result
    source.root (UInt64.ofNat grid.size) hParams hSaved]
  rw [← List.append_assoc]
  apply initial_map_allocate_spec env store heap params prepared tail hParams hPrepared hTail hStart
    requested previous current capacity next result n grid.size source grid hHeap hOwner
    (Option.map_eq_none_iff.mp ((takeFirstFitFrom_project 0 requested heap.nodes).trans
      (initialFreeBelow_none grid.size hCount heap.nodes hBelow)))
    (by rw [hRequested]; simp only [initialBytes]; omega)
    (by simpa only [hRequested] using hFit32) hPages hCap hn hSum
  · exact (hPreserved 1 (by decide)).trans
      ((initial_map_input_get_other frame source.root (UInt64.ofNat grid.size) 1 hFrameParams
        (by decide) (by decide) (by decide)).trans hN)
  · exact (hPreserved 10 (by decide)).trans hGets.1
  · exact (hPreserved 48 (by decide)).trans hGets.2.1
  · exact (hPreserved 49 (by decide)).trans hGets.2.2
  · exact hNext

#print axioms initial_map_program_shape
#print axioms initial_map_program_spec

end Project.EulerRiemann.Execution
