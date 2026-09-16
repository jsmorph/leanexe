import Project.EulerCertificate.AdvanceTotalIteration

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann
open Project.EulerRiemann.Execution
open Project.EulerCertificate.Control (Result)
open Wasm Project.Runtime Project.ProofKit

theorem advance_total_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (trials startTime : UInt64) (expected : Result) (spare limit pageLimit : Nat)
    (store : Store Unit) (frame : Locals) (hn : 2 ≤ n ∧ n ≤ 800)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPageLimit : pageLimit ≤ 65536) (hLimitPages : limit ≤ pageLimit * 65536)
    (hInv : advanceTotalInvariant initial initialHeap n trials startTime expected spare limit pageLimit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final heap resultFrame,
      RetryStoreAt initial initialHeap final heap → final.mem.pages ≤ pageLimit →
      AdvanceTotalDone initial initialHeap n startTime expected spare limit final heap resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 advanceLoop]] ++ rest) Q store frame env := by
  refine BlockLoop.program_spec module env store frame advanceLoop
    (advanceTotalInvariant initial initialHeap n trials startTime expected spare limit pageLimit)
    (fun final resultFrame => ∃ heap, RetryStoreAt initial initialHeap final heap ∧ final.mem.pages ≤ pageLimit ∧
      AdvanceTotalDone initial initialHeap n startTime expected spare limit final heap resultFrame)
    (fun _ current => advanceMeasure current) (fun _ _ h => h.values) ?_ hInv ?_ Q rest ?_
  · intro final resultFrame ⟨heap, _, _, source, tracked, hFrame, _⟩
    exact hFrame.values
  · intro current currentFrame hCurrent
    exact advance_total_iteration_spec env initial initialHeap n trials startTime expected spare limit pageLimit
      current currentFrame hn hLimit hCap hPageLimit hLimitPages hCurrent
  · intro final resultFrame ⟨heap, hStore, hPages, hDone⟩
    exact hNext final heap resultFrame hStore hPages hDone

#print axioms advance_total_loop_spec

end Project.EulerCertificate.Execution
