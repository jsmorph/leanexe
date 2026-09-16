import Project.EulerCertificate.OutputCertificateData
import Project.EulerCertificate.ArrayAllocation
import Project.ProofKit.FixedArraySearchProjection

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit
open Project.EulerRiemann Project.EulerRiemann.Execution
open Project.EulerCertificate.Flux (Vector)

theorem output_certificate_allocate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value)
    (hParams : params.length = 17) (hSaved : saved.length = 35) (hTail : tail.length = 7)
    (hStart : params.length + saved.length = 52)
    (need previous current capacity next result : UInt64) (r : Vector)
    (hHeap : heap.At store) (hNeed : 104 ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (hInputs : ∀ i : Fin 12,
      ({ params := params, locals := saved, values := [] } : Locals).get (26 + i.val) =
        some (.i64 ((Solve.certificateWords r)[i.val]'(by simpa only [Solve.certificateWords,
          List.length_cons, List.length_nil] using i.isLt))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next final,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes)
        (outputCertificateWords r) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 104) →
      wp module rest Q final (outputCertificateResultFrame
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) (allocatedRoot heap.top need heap.nodes) r) env) :
    wp module (FixedArrayAllocate.program 52 1 ++ outputCertificateDataProgram ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply heap_array_allocation_program_spec env store heap params saved tail 52 hStart
    need 1 previous current capacity next result hHeap
    (fun hNone => ⟨(hBump hNone).1.le, (hBump hNone).2⟩) hPages
  intro previousAfter currentAfter capacityAfter nextAfter
  let frame := FixedArraySearch.frame params saved tail need previousAfter currentAfter capacityAfter
    nextAfter (allocatedRoot heap.top need heap.nodes)
  have hFrameLocals : frame.locals.length = 48 := by
    simp only [frame, FixedArraySearch.frame, List.length_append, List.length_cons,
      List.length_nil, hSaved, hTail]
  have hRoot : frame.get 57 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved tail need previousAfter currentAfter
      capacityAfter nextAfter (allocatedRoot heap.top need heap.nodes) 5 (by decide)
    simpa only [hStart, Nat.reduceAdd, List.getElem?_cons_zero, List.getElem?_cons_succ] using hGet
  apply output_certificate_owned_spec env store heap frame need r hHeap hNeed
    (fun hNone => (hBump hNone).1) hParams hFrameLocals rfl
  · intro i
    exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ (26 + i.val) (by omega)).trans (hInputs i)
  · exact hRoot
  · intro final hFinalHeap hOwner hWrites
    exact hNext previousAfter currentAfter capacityAfter nextAfter final hFinalHeap hOwner hWrites

#print axioms output_certificate_allocate_spec
end Project.EulerCertificate.Execution
