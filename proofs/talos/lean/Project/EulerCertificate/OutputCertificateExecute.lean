import Project.EulerCertificate.OutputCertificateAllocate
import Project.ProofKit.FixedArraySearchPrepare
import Project.ProofKit.I64LocalRange

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayCapacity FixedArrayFold
open Project.EulerRiemann Project.EulerRiemann.Execution
open Project.EulerCertificate.Flux (Vector)

set_option maxRecDepth 4096

def outputCertificateProgram : Wasm.Program := (func15.drop 46).take 207

theorem output_certificate_shape : outputCertificateProgram = constantProgram 12 1 52 ++
    FixedArrayAllocate.program 52 1 ++ outputCertificateDataProgram := rfl

theorem output_certificate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (r : Vector)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 48 65)
    (hInputs : ∀ i : Fin 12, frame.get (26 + i.val) =
      some (.i64 ((Solve.certificateWords r)[i.val]'(by simpa only [Solve.certificateWords,
        List.length_cons, List.length_nil] using i.isLt))))
    (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 104 heap.nodes = none →
      heap.top.toNat + 152 < 4294967296 ∧ bumpPages heap.top 104 ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      (heap.allocate 104).At final →
      (heap.allocate 104).OwnsWords final (allocatedNode heap.top 104 heap.nodes)
        (outputCertificateWords r) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store 104 1) final
        (allocatedRoot heap.top 104 heap.nodes).toNat
        ((allocatedRoot heap.top 104 heap.nodes).toNat + 104) →
      result.params = frame.params → result.locals.length = 48 → result.values = [] →
      I64LocalRange result 48 65 →
      result.get 48 = some (.i64 (allocatedRoot heap.top 104 heap.nodes)) →
      (∀ index : Nat, index < 48 → result.get index = frame.get index) →
      wp module rest Q final result env) :
    wp module (outputCertificateProgram ++ rest) Q store frame env := by
  have hSaved : (frame.locals.take 35).length = 35 := by simp [hLocals]
  have hTail : (frame.locals.drop 41).length = 7 := by simp [hLocals]
  have hStart : frame.params.length + (frame.locals.take 35).length = 52 := by omega
  obtain ⟨need, previous, current, capacity, next, root, hEq⟩ :=
    hScratch.window 35 (by omega) (by omega) (by omega) hValues
  have hBefore (index : Nat) (hIndex : index < 52) :
      ({ params := frame.params, locals := frame.locals.take 35, values := [] } : Locals).get index =
        frame.get index := by
    have hGet := FixedArraySearch.frame_get_before frame.params (frame.locals.take 35) (frame.locals.drop 41)
      need previous current capacity next root index (by omega)
    rw [← hEq] at hGet
    exact hGet.symm
  have hCapacity : normalizedCapacity 12 1 = 104 := by decide
  rw [output_certificate_shape, List.append_assoc, List.append_assoc]
  apply constantProgram_spec 12 1 52 module env store frame hValues (by omega)
    (by simp [Locals.validIndex, hParams, hLocals])
  rw [hCapacity, hEq]
  have hCapacityFrame := FixedArraySearch.capacityFrame_need frame.params (frame.locals.take 35)
    (frame.locals.drop 41) need previous current capacity next root 104
  rw [hStart] at hCapacityFrame
  rw [hCapacityFrame]
  apply output_certificate_allocate_spec env store heap frame.params (frame.locals.take 35)
    (frame.locals.drop 41) hParams hSaved hTail hStart 104 previous current capacity next root r hHeap (by decide)
    (by intro hNone; have h := hBump hNone; exact ⟨by simpa [Nat.add_assoc] using h.1, h.2⟩)
    hPages (fun i => (hBefore (26 + i.val) (by omega)).trans (hInputs i))
  intro previousAfter currentAfter capacityAfter nextAfter final hFinalHeap hOwner hWrites
  let allocated := FixedArraySearch.frame frame.params (frame.locals.take 35) (frame.locals.drop 41)
    104 previousAfter currentAfter capacityAfter nextAfter (allocatedRoot heap.top 104 heap.nodes)
  have hAllocatedParams : allocated.params.length = 17 := hParams
  have hAllocatedLocals : allocated.locals.length = 48 := by
    simp [allocated, FixedArraySearch.frame, hSaved, hTail]
  have hValid (index : Nat) (hi : index < 65) : allocated.validIndex index := by
    simp only [Locals.validIndex, hAllocatedParams, hAllocatedLocals]
    exact hi
  have hAllocatedScratch : I64LocalRange allocated 48 65 := by
    have hOriginal := hScratch
    rw [hEq] at hOriginal
    exact hOriginal.search 104 previousAfter currentAfter capacityAfter nextAfter _
  apply hNext final (outputCertificateResultFrame allocated (allocatedRoot heap.top 104 heap.nodes) r)
    hFinalHeap hOwner hWrites rfl
  · simpa only [outputCertificateResultFrame, resultFrame_locals_length] using hAllocatedLocals
  · rfl
  · exact (hAllocatedScratch.result 48 _ (by omega) (hValid 48 (by decide))).result 51 r.energy.upper
      (by simpa only [resultFrame_params] using (show allocated.params.length ≤ 51 by omega))
      (by simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length]
        using hValid 51 (by decide))
  · rw [outputCertificateResultFrame, resultFrame_get_ne _ 51 48 _
      (by change allocated.params.length ≤ 51; omega) (by decide)]
    exact resultFrame_get_result allocated 48 _ (by omega) (hValid 48 (by decide))
  · intro index hIndex
    rw [outputCertificateResultFrame,
      resultFrame_get_ne _ 51 index _ (by change allocated.params.length ≤ 51; omega) (by omega),
      resultFrame_get_ne _ 48 index _ (by omega) (by omega)]
    exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ index (by omega)).trans
      (hBefore index (by omega))

#print axioms output_certificate_shape
#print axioms output_certificate_spec
end Project.EulerCertificate.Execution
