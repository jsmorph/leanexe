import Project.EulerCertificate.OutputCertificateExecute
import Project.EulerCertificate.OutputAppendExecute
import Project.EulerCertificate.OutputTail

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCapacity
open Project.EulerRiemann Project.EulerRiemann.Execution
open Project.EulerCertificate.Flux (Vector)

set_option maxRecDepth 4096

def certificateOutputBytes (size : Nat) : Nat := 152 + (48 + 8 * (size + 12 + 1))

theorem output_compose_shape : func15.drop 46 = outputCertificateProgram ++
    resultProgram 48 39 ++ resultProgram 39 40 ++ outputAppendProgram ++ outputTailProgram := rfl

theorem output_compose_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (frame : Locals)
    (base : FreeNode) (words : Array UInt64) (r : Vector) (pageLimit : Nat)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48)
    (hValues : frame.values = []) (hScratch : I64LocalRange frame 48 65)
    (hBaseOwnerLocal : frame.get 24 = some (.i64 base.root))
    (hBasePointerLocal : frame.get 25 = some (.i64 base.root))
    (hInputs : ∀ i : Fin 12, frame.get (26 + i.val) =
      some (.i64 ((Solve.certificateWords r)[i.val]'(by simpa only [Solve.certificateWords,
        List.length_cons, List.length_nil] using i.isLt))))
    (hHeap : heap.At store) (hBase : heap.OwnsWords store base words) (hSize : words.size ≤ 1280004)
    (hBudget : OutputBudget store heap (certificateOutputBytes words.size) pageLimit)
    (Q : Assertion Unit)
    (hNext : ∀ final finalHeap result resultFrame,
      finalHeap.At final → finalHeap.OwnsWords final result (words ++ outputCertificateWords r) →
      OutputBudget final finalHeap 0 pageLimit → resultFrame.values = [.i64 result.root, .i64 result.root] →
      Q (.Fallthrough final resultFrame)) :
    wp module (func15.drop 46) Q store frame env := by
  let certHeap := heap.allocate 104
  let certificate := allocatedNode heap.top 104 heap.nodes
  let need := normalizedCapacity (UInt64.ofNat (words.size + 12)) 1
  have hCertificateSize : (outputCertificateWords r).size = 12 := rfl
  have hNeed : need.toNat = 8 * (words.size + 12 + 1) := certificate_word_capacity _ (by omega)
  have hBumpC := hBudget.bump 104 (by unfold certificateOutputBytes; change 48 + 104 ≤ _; omega)
  have hSeparate := hBase.allocation_disjoint 104 (fun hNone => (hBumpC hNone).1.le)
  rw [output_compose_shape]
  simp only [List.append_assoc]
  apply output_certificate_spec env store heap frame r hParams hLocals hValues hScratch hInputs hHeap
    (by intro hNone; have h := hBumpC hNone; exact ⟨by simpa [Nat.add_assoc] using h.1, h.2⟩)
    (hBudget.pages.trans hBudget.pageLimitBound)
  intro current certFrame hCertHeap hCertOwner hWritesC hCertParamsEq hCertLocals hCertValues
    hCertScratch hCertRoot hPreserved
  have hCertParams : certFrame.params.length = 17 := (congrArg List.length hCertParamsEq).trans hParams
  have hBudgetC : OutputBudget current certHeap (48 + need.toNat) pageLimit :=
    hBudget.allocated 104 1 _ (by rw [hNeed]; unfold certificateOutputBytes; change 48 + 104 + _ ≤ _; omega) hWritesC
  have hBaseC : certHeap.OwnsWords current base words :=
    hBase.arrayWritten 104 1 12 hHeap (by decide) (fun hNone => (hBumpC hNone).1.le) hWritesC
  have hBumpR := hBudgetC.bump need (Nat.le_refl _)
  have hBaseTarget := hBaseC.allocation_disjoint need (fun hNone => (hBumpR hNone).1.le)
  have hCertTarget := hCertOwner.allocation_disjoint need (fun hNone => (hBumpR hNone).1.le)
  let first := resultFrame certFrame 39 certificate.root
  let ready := resultFrame first 40 certificate.root
  have hValid (i : Nat) (hi : i < 65) : certFrame.validIndex i := by
    simpa only [Locals.validIndex, hCertParams, hCertLocals] using hi
  have hFirstRoot : first.get 39 = some (.i64 certificate.root) :=
    resultFrame_get_result certFrame 39 certificate.root (by omega) (hValid 39 (by decide))
  have hFirstParams : first.params.length = 17 := hCertParams
  have hFirstLocals : first.locals.length = 48 := by simpa only [first, resultFrame_locals_length] using hCertLocals
  have hReadyParams : ready.params.length = 17 := hFirstParams
  have hReadyLocals : ready.locals.length = 48 := by simpa only [ready, resultFrame_locals_length] using hFirstLocals
  have hValid40 : first.validIndex 40 := by simp [Locals.validIndex, hFirstParams, hFirstLocals]
  have hReadyScratch : I64LocalRange ready 48 65 :=
    (hCertScratch.result 39 certificate.root (by omega) (hValid 39 (by decide))).result 40 certificate.root
      (by change certFrame.params.length ≤ 40; omega) hValid40
  have hReadyBase (i : Nat) (hi : i = 24 ∨ i = 25) : ready.get i = frame.get i := by
    dsimp only [ready, first]
    rw [resultFrame_get_ne _ 40 i _ (by change certFrame.params.length ≤ 40; omega) (by omega),
      resultFrame_get_ne _ 39 i _ (by omega) (by omega)]
    exact hPreserved i (by omega)
  have hReadyOwner : ready.get 39 = some (.i64 certificate.root) :=
    (resultFrame_get_ne first 40 39 _ (by omega) (by decide)).trans hFirstRoot
  have hReadyPointer : ready.get 40 = some (.i64 certificate.root) :=
    resultFrame_get_result first 40 _ (by omega) hValid40
  apply resultProgram_spec 48 39 module env current certFrame certificate.root hCertValues hCertRoot
    (by omega) (hValid 39 (by decide))
  apply resultProgram_spec 39 40 module env current first certificate.root rfl hFirstRoot (by omega) hValid40
  apply output_append_spec env current certHeap ready base certificate words (outputCertificateWords r)
    hReadyParams hReadyLocals rfl hReadyScratch
    ((hReadyBase 25 (Or.inr rfl)).trans hBasePointerLocal) hReadyPointer
    hCertHeap hBaseC hCertOwner (by rw [hCertificateSize]; omega)
    (by simp only [hCertificateSize]; exact hBumpR) (hBudgetC.pages.trans hBudgetC.pageLimitBound)
  dsimp only
  intro final resultFrame hFinalHeap hFinalBase hFinalCertificate hFinalOwner hWritesR
    hResultParams hResultLocals hResultValues hResultScratch hResultRoot hResultPreserved
  simp only [hCertificateSize] at hFinalHeap hFinalBase hFinalCertificate hFinalOwner hWritesR hResultRoot
  have hBudgetR : OutputBudget final (certHeap.allocate need) 0 pageLimit :=
    hBudgetC.allocated need 1 0 (by omega) hWritesR
  apply output_tail_spec env final (certHeap.allocate need) resultFrame base certificate
    (allocatedNode certHeap.top need certHeap.nodes) words (outputCertificateWords r) pageLimit
    hResultParams hResultLocals hResultValues
    ((hResultPreserved 24 (by decide) (by decide)).trans ((hReadyBase 24 (Or.inl rfl)).trans hBaseOwnerLocal))
    ((hResultPreserved 39 (by decide) (by decide)).trans hReadyOwner) hResultRoot
    hFinalHeap hFinalBase hFinalCertificate hFinalOwner hSeparate hBaseTarget hCertTarget hBudgetR
  intro finished finalHeap finalFrame hHeapFinished hOwnerFinished hBudgetFinished hValuesFinished
  exact hNext finished finalHeap _ finalFrame hHeapFinished hOwnerFinished hBudgetFinished hValuesFinished

#print axioms output_compose_shape
#print axioms output_compose_spec
end Project.EulerCertificate.Execution
