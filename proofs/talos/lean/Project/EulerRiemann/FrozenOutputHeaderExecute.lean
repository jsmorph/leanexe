import Project.EulerRiemann.FrozenOutputHeaderAllocate
import Project.ProofKit.FixedArraySearchPrepare
import Project.ProofKit.I64LocalRange

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity FixedArrayFold

def outputHeaderProgram : Wasm.Program := (func99.drop 185).take 95

theorem output_header_shape : outputHeaderProgram = constantProgram 4 1 51 ++
    FixedArrayAllocate.program 51 1 ++ outputHeaderDataProgram := rfl

theorem output_header_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (n time status : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 42 57)
    (hN : frame.get 0 = some (.i64 n)) (hTime : frame.get 1 = some (.i64 time))
    (hStatus : frame.get 2 = some (.i64 status)) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 40 heap.nodes = none →
      heap.top.toNat + 88 < 4294967296 ∧ bumpPages heap.top 40 ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      (heap.allocate 40).At final →
      (heap.allocate 40).OwnsWords final (allocatedNode heap.top 40 heap.nodes)
        (outputHeaderWords n time status) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store 40 1) final
        (allocatedRoot heap.top 40 heap.nodes).toNat
        ((allocatedRoot heap.top 40 heap.nodes).toNat + 40) →
      result.params = frame.params → result.locals.length = 52 → result.values = [] →
      I64LocalRange result 42 57 →
      result.get 47 = some (.i64 (allocatedRoot heap.top 40 heap.nodes)) →
      (∀ index : Nat, index < 47 → result.get index = frame.get index) →
      wp module rest Q final result env) :
    wp module (outputHeaderProgram ++ rest) Q store frame env := by
  have hSaved : (frame.locals.take 46).length = 46 := by simp [hLocals]
  have hTail : frame.locals.drop 52 = [] := by simp [List.drop_eq_nil_iff, hLocals]
  have hStart : frame.params.length + (frame.locals.take 46).length = 51 := by omega
  obtain ⟨need, previous, current, capacity, next, root, hEq⟩ :=
    hScratch.window 46 (by omega) (by omega) (by omega) hValues
  simp only [hTail] at hEq
  have hBefore (index : Nat) (hIndex : index < 51) :
      ({ params := frame.params, locals := frame.locals.take 46, values := [] } : Locals).get index =
        frame.get index := by
    have hGet := FixedArraySearch.frame_get_before frame.params (frame.locals.take 46) []
      need previous current capacity next root index (by omega)
    rw [← hEq] at hGet
    exact hGet.symm
  have hCapacity : normalizedCapacity 4 1 = 40 := by decide
  rw [output_header_shape, List.append_assoc, List.append_assoc]
  apply constantProgram_spec 4 1 51 module env store frame hValues (by omega)
    (by simp [Locals.validIndex, hParams, hLocals])
  rw [hCapacity, hEq]
  have hCapacityFrame := FixedArraySearch.capacityFrame_need frame.params (frame.locals.take 46) []
    need previous current capacity next root 40
  rw [hStart] at hCapacityFrame
  rw [hCapacityFrame]
  apply output_header_allocate_spec env store heap frame.params (frame.locals.take 46)
    hParams hSaved hStart 40 previous current capacity next root n time status hHeap (by decide)
    (by intro hNone; have h := hBump hNone; exact ⟨by simpa [Nat.add_assoc] using h.1, h.2⟩)
    hPages ((hBefore 0 (by decide)).trans hN) ((hBefore 1 (by decide)).trans hTime)
    ((hBefore 2 (by decide)).trans hStatus)
  intro previousAfter currentAfter capacityAfter nextAfter final hFinalHeap hOwner hWrites
  let allocated := FixedArraySearch.frame frame.params (frame.locals.take 46) [] 40 previousAfter
    currentAfter capacityAfter nextAfter (allocatedRoot heap.top 40 heap.nodes)
  have hAllocatedParams : allocated.params.length = 5 := hParams
  have hAllocatedLocals : allocated.locals.length = 52 := by
    simp [allocated, FixedArraySearch.frame, hSaved]
  have hValid (index : Nat) (hi : index < 57) : allocated.validIndex index := by
    simp only [Locals.validIndex, hAllocatedParams, hAllocatedLocals]
    exact hi
  have hAllocatedScratch : I64LocalRange allocated 42 57 := by
    have hOriginal := hScratch
    rw [hEq] at hOriginal
    exact hOriginal.search 40 previousAfter currentAfter capacityAfter nextAfter _
  apply hNext final (outputHeaderResultFrame allocated (allocatedRoot heap.top 40 heap.nodes) n)
    hFinalHeap hOwner hWrites rfl
  · simpa only [outputHeaderResultFrame, resultFrame_locals_length] using hAllocatedLocals
  · rfl
  · exact (hAllocatedScratch.result 47 _ (by omega) (hValid 47 (by decide))).result 50 n
      (by simpa only [resultFrame_params] using (show allocated.params.length ≤ 50 by omega))
      (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length]
        using hValid 50 (by decide))
  · rw [outputHeaderResultFrame, resultFrame_get_ne _ 50 47 _
      (by change allocated.params.length ≤ 50; omega) (by decide)]
    exact resultFrame_get_result allocated 47 _ (by omega) (hValid 47 (by decide))
  · intro index hIndex
    rw [outputHeaderResultFrame,
      resultFrame_get_ne _ 50 index _ (by change allocated.params.length ≤ 50; omega) (by omega),
      resultFrame_get_ne _ 47 index _ (by omega) (by omega)]
    exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ index (by omega)).trans
      (hBefore index (by omega))

#print axioms output_header_shape
#print axioms output_header_spec

end Project.EulerRiemann.Frozen.Execution
