import Project.EulerCertificate.OutputRelease
import Project.EulerRiemann.OutputBudget

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold
open Project.EulerRiemann Project.EulerRiemann.Execution

set_option maxRecDepth 4096

def outputTailProgram : Wasm.Program := func15.drop 328

theorem output_tail_shape : outputTailProgram = resultProgram 42 43 ++
    outputReleaseProgram 24 44 ++ outputReleaseProgram 39 45 ++
    [.localGet 42, .localSet 46, .localGet 43, .localSet 47, .localGet 46, .localGet 47] := rfl

theorem output_tail_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (frame : Locals)
    (source certificate target : FreeNode) (left right : Array UInt64) (pageLimit : Nat)
    (hParams : frame.params.length = 17) (hLocals : frame.locals.length = 48) (hValues : frame.values = [])
    (hSource : frame.get 24 = some (.i64 source.root))
    (hCertificate : frame.get 39 = some (.i64 certificate.root))
    (hTarget : frame.get 42 = some (.i64 target.root))
    (hHeap : heap.At store) (hSourceOwner : heap.OwnsWords store source left)
    (hCertificateOwner : heap.OwnsWords store certificate right)
    (hTargetOwner : heap.OwnsWords store target (left ++ right))
    (hSeparate : regionsDisjoint source.region certificate.region)
    (hSourceTarget : regionsDisjoint source.region target.region)
    (hCertificateTarget : regionsDisjoint certificate.region target.region)
    (hBudget : OutputBudget store heap 0 pageLimit) (Q : Assertion Unit)
    (hNext : ∀ final finalHeap resultFrame,
      finalHeap.At final → finalHeap.OwnsWords final target (left ++ right) →
      OutputBudget final finalHeap 0 pageLimit → resultFrame.values = [.i64 target.root, .i64 target.root] →
      Q (.Fallthrough final resultFrame)) :
    wp module outputTailProgram Q store frame env := by
  have hValid (i : Nat) (hi : i < 65) : frame.validIndex i := by
    simpa only [Locals.validIndex, hParams, hLocals] using hi
  have hSource32 : source.root.toNat ≤ 4294967296 := by
    have := hSourceOwner.buffer.addressBound
    omega
  have hCertificateAfter := hCertificateOwner.released source hSourceOwner.buffer.rootBound hSource32
    (regionsDisjoint_symm hSeparate)
  have hTargetAfter := hTargetOwner.released source hSourceOwner.buffer.rootBound hSource32
    (regionsDisjoint_symm hSourceTarget)
  let copied := resultFrame frame 43 target.root
  have hCopiedParams : copied.params.length = 17 := hParams
  have hCopiedLocals : copied.locals.length = 48 := by simpa only [copied, resultFrame_locals_length] using hLocals
  have hCopiedSource : copied.get 24 = some (.i64 source.root) :=
    (resultFrame_get_ne frame 43 24 _ (by omega) (by decide)).trans hSource
  rw [output_tail_shape]
  simp only [List.append_assoc]
  apply resultProgram_spec 42 43 module env store frame target.root hValues hTarget (by omega) (hValid 43 (by decide))
  apply output_release_spec env store heap copied source left 24 44 hHeap hSourceOwner rfl hCopiedSource
    (by omega) (by simp [Locals.validIndex, hCopiedParams, hCopiedLocals])
  intro hAfterSource
  let released := resultFrame copied 44 (heap.frees + 1)
  have hReleasedParams : released.params.length = 17 := hCopiedParams
  have hReleasedLocals : released.locals.length = 48 := by simpa only [released, resultFrame_locals_length] using hCopiedLocals
  have hReleasedCertificate : released.get 39 = some (.i64 certificate.root) := by
    dsimp only [released, copied]
    rw [resultFrame_get_ne _ 44 39 _ (by change frame.params.length ≤ 44; omega) (by decide),
      resultFrame_get_ne _ 43 39 _ (by omega) (by decide)]
    exact hCertificate
  apply output_release_spec env (heap.releaseStore store source) (heap.release source) released certificate right 39 45
    hAfterSource hCertificateAfter rfl hReleasedCertificate (by omega)
    (by simp [Locals.validIndex, hReleasedParams, hReleasedLocals])
  intro hAfterCertificate
  have hCertificate32 : certificate.root.toNat ≤ 4294967296 := by
    have := hCertificateAfter.buffer.addressBound
    omega
  have hFinalOwner := hTargetAfter.released certificate hCertificateAfter.buffer.rootBound hCertificate32
    (regionsDisjoint_symm hCertificateTarget)
  have hLocal42 : frame.locals[25]? = some (.i64 target.root) := by
    simpa only [Locals.get, hParams, hLocals, reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub] using hTarget
  wp_run [released, copied, resultFrame, hParams, hLocals, hValues, hLocal42,
    List.length_set, List.getElem?_set, reduceIte, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff]
  exact hNext _ _ _ hAfterCertificate hFinalOwner ((hBudget.released source).released certificate) rfl

#print axioms output_tail_shape
#print axioms output_tail_spec
end Project.EulerCertificate.Execution
