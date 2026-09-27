import Project.EulerRiemann.OutputMapReturn

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCapacity

def outputMapProgram (pressure : Bool) : Wasm.Program :=
  (func99.drop (if pressure then 52 else 0)).take 52

theorem output_map_shape (pressure : Bool) : outputMapProgram pressure =
    outputMapPrepareProgram ++ FixedArrayAllocate.program 42 1 ++
      outputMapDataProgram pressure ++ outputMapReturnProgram pressure := by
  cases pressure <;> rfl

theorem output_map_spec (pressure : Bool) (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (source : FreeNode) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 42 57)
    (hSource : frame.get 4 = some (.i64 source.root))
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid) (hSize : grid.size ≤ 640000)
    (hBump : let need := normalizedCapacity (UInt64.ofNat grid.size) 1
      takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : let need := normalizedCapacity (UInt64.ofNat grid.size) 1
      let target := allocatedNode heap.top need heap.nodes
      ∀ final result,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).OwnsWords final target (outputMapResult pressure grid) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store need 1) final
        target.root.toNat (target.root.toNat + 8 * (grid.size + 1)) →
      result.params.length = 5 → result.locals.length = 52 → result.values = [] →
      I64LocalRange result 42 57 →
      result.get (outputMapOwnerLocal pressure) = some (.i64 target.root) →
      result.get (outputMapOwnerLocal pressure + 1) = some (.i64 target.root) →
      (∀ index : Nat, index < 36 →
        (index < outputItemStart pressure ∨ outputItemStart pressure + 7 ≤ index) →
        index ≠ outputMapOwnerLocal pressure → index ≠ outputMapOwnerLocal pressure + 1 →
        result.get index = frame.get index) →
      wp module rest Q final result env) :
    wp module (outputMapProgram pressure ++ rest) Q store frame env := by
  let need := normalizedCapacity (UInt64.ofNat grid.size) 1
  let prepared := outputMapPreparedFrame frame source.root (UInt64.ofNat grid.size)
  have hPreparedParams : prepared.params.length = 5 := hParams
  have hPreparedLocals : prepared.locals.length = 52 := by
    simpa only [prepared, outputMapPreparedFrame, resultFrame_locals_length] using hLocals
  have hPreparedScratch := output_map_prepared_scratch frame source.root (UInt64.ofNat grid.size)
    hParams hLocals hScratch
  change I64LocalRange prepared 42 57 at hPreparedScratch
  have hGets := output_map_prepared_gets frame source.root (UInt64.ofNat grid.size) hParams hLocals
  change prepared.get 36 = some (.i64 source.root) ∧ prepared.get 37 = some (.i64 (UInt64.ofNat grid.size)) ∧
    prepared.get 42 = some (.i64 need) at hGets
  have hSaved : (prepared.locals.take 37).length = 37 := by simp [hPreparedLocals]
  have hTail : (prepared.locals.drop 43).length = 9 := by simp [hPreparedLocals]
  have hStart : prepared.params.length + (prepared.locals.take 37).length = 42 := by omega
  obtain ⟨requested, previous, current, capacity, next, root, hEq⟩ :=
    hPreparedScratch.window 37 (by omega) (by omega) (by omega) rfl
  have hNeedGet := FixedArraySearch.frame_get prepared.params (prepared.locals.take 37)
    (prepared.locals.drop 43) requested previous current capacity next root 0 (by decide)
  simp only [hStart, Nat.add_zero, List.getElem?_cons_zero] at hNeedGet
  rw [← hEq, hGets.2.2] at hNeedGet
  have hRequested : requested = need := (Value.i64.inj (Option.some.inj hNeedGet)).symm
  subst requested
  have hBefore (index : Nat) (hi : index < 42) :
      ({ params := prepared.params, locals := prepared.locals.take 37, values := [] } : Locals).get index =
        prepared.get index := by
    have hGet := FixedArraySearch.frame_get_before prepared.params (prepared.locals.take 37)
      (prepared.locals.drop 43) need previous current capacity next root index (by omega)
    rw [← hEq] at hGet
    exact hGet.symm
  have hNeed : 8 * (grid.size + 1) ≤ need.toNat :=
    (output_word_capacity grid.size (by omega)).ge
  rw [output_map_shape]
  simp only [List.append_assoc]
  apply output_map_prepare_spec env store frame source.root grid hParams hLocals hValues hSource
    hOwner.buffer.values
  change wp module (FixedArrayAllocate.program 42 1 ++ (outputMapDataProgram pressure ++
    (outputMapReturnProgram pressure ++ rest))) Q store prepared env
  rw [hEq]
  apply output_map_allocate_spec pressure env store heap prepared.params (prepared.locals.take 37)
    (prepared.locals.drop 43) hPreparedParams hSaved hTail hStart need previous current capacity next root
    source grid hHeap hOwner hNeed hBump hPages
    ((hBefore 36 (by decide)).trans hGets.1) ((hBefore 37 (by decide)).trans hGets.2.1)
  intro previousAfter currentAfter capacityAfter nextAfter final mapped hFinalHeap hSourceOwner hResultOwner
    hWrites hMapped
  let target := allocatedRoot heap.top need heap.nodes
  let allocated := FixedArraySearch.frame prepared.params (prepared.locals.take 37)
    (prepared.locals.drop 43) need previousAfter currentAfter capacityAfter nextAfter target
  have hAllocatedParams : allocated.params.length = 5 := hPreparedParams
  have hAllocatedLocals : allocated.locals.length = 52 := by
    simp [allocated, FixedArraySearch.frame, hSaved, hTail]
  have hCounter : allocated.validIndex 39 := by
    simp [Locals.validIndex, hAllocatedParams, hAllocatedLocals]
  have hAllocatedScratch : I64LocalRange allocated 42 57 := by
    have hOriginal := hPreparedScratch
    rw [hEq] at hOriginal
    exact hOriginal.search need previousAfter currentAfter capacityAfter nextAfter target
  have hItem : outputItemStart pressure + 7 ≤ 36 := by cases pressure <;> decide
  have hReadyScratch : I64LocalRange (outputMapReadyFrame allocated target hCounter) 42 57 := by
    apply hAllocatedScratch.of_preserved
    intro index hFirst hLast
    exact output_map_ready_get allocated target hCounter hAllocatedParams index (by omega) (by omega)
  have hMappedScratch : I64LocalRange mapped 42 57 := by
    apply hReadyScratch.of_preserved
    intro index hFirst hLast
    exact hMapped.preserved index (Or.inr (by omega)) (by omega)
  have hTarget : mapped.get 38 = some (.i64 target) := by
    rw [hMapped.preserved 38 (Or.inr (by omega)) (by decide)]
    exact output_map_ready_target allocated target hCounter hAllocatedParams
  apply output_map_return_spec pressure env final mapped target hMapped.paramsLength hMapped.localsLength
    hMapped.values hTarget
  have hReturned := output_map_return_gets pressure mapped target hMapped.paramsLength hMapped.localsLength
  apply hNext final (outputMapReturnedFrame pressure mapped target) hFinalHeap hSourceOwner hResultOwner hWrites
  · exact hMapped.paramsLength
  · simpa only [outputMapReturnedFrame, resultFrame_locals_length] using hMapped.localsLength
  · rfl
  · exact output_map_return_scratch pressure mapped target hMapped.paramsLength hMappedScratch
  · exact hReturned.1
  · exact hReturned.2
  · intro index hi hField hOwnerLocal hPointerLocal
    rw [output_map_return_get_other pressure mapped target index hMapped.paramsLength hOwnerLocal hPointerLocal,
      hMapped.preserved index hField (by omega)]
    change (outputMapReadyFrame allocated target hCounter).get index = frame.get index
    rw [output_map_ready_get allocated target hCounter hAllocatedParams index (by omega) (by omega)]
    have hAllocatedGet := FixedArraySearch.frame_get_before prepared.params (prepared.locals.take 37)
      (prepared.locals.drop 43) need previousAfter currentAfter capacityAfter nextAfter target index (by omega)
    exact hAllocatedGet.trans ((hBefore index (by omega)).trans
      (output_map_prepared_get_other frame source.root (UInt64.ofNat grid.size) index hParams
        (by omega) (by omega) (by omega)))

#print axioms output_map_shape
#print axioms output_map_spec

end Project.EulerRiemann.Execution
