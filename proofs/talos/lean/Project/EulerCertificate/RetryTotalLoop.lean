import Project.EulerCertificate.RetryTotalIteration

namespace Project.EulerCertificate.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity
open Project.EulerRiemann.Execution
open Project.EulerCertificate.Control (Attempt)

theorem retry_total_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Project.EulerRiemann.Traversal.Cell) (n : Nat) (trials time alpha : UInt64)
    (expected : Attempt) (spare limit pageLimit : Nat) (store : Store Unit) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Project.EulerRiemann.Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hPageLimit : pageLimit ≤ 65536) (hLimitPages : limit ≤ pageLimit * 65536)
    (hInv : retryTotalInvariant initial initialHeap n trials time alpha source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final heap resultFrame,
      RetryStoreAt initial initialHeap final heap → final.mem.pages ≤ pageLimit →
      RetryTotalStopped initial initialHeap n trials time alpha source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit final heap resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 retryLoop]] ++ rest) Q store frame env := by
  refine Project.ProofKit.BlockLoop.program_spec module env store frame retryLoop
    (retryTotalInvariant initial initialHeap n trials time alpha source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit pageLimit)
    (fun final resultFrame => ∃ heap, RetryStoreAt initial initialHeap final heap ∧ final.mem.pages ≤ pageLimit ∧
      RetryTotalStopped initial initialHeap n trials time alpha source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit final heap resultFrame)
    (fun _ current => retryMeasure current) (fun _ _ h => h.values) ?_ hInv ?_ Q rest ?_
  · intro final resultFrame ⟨heap, _, _, hDone⟩
    exact hDone.values
  · intro current currentFrame hCurrent
    exact retry_total_iteration_spec env initial initialHeap source grid n trials time alpha expected
      spare limit pageLimit current currentFrame hn hIndexed hOwner hLimit hCap hPageLimit hLimitPages hCurrent
  · intro final resultFrame ⟨heap, hStore, hPages, hDone⟩
    exact hNext final heap resultFrame hStore hPages hDone

#print axioms retry_total_loop_spec

end Project.EulerCertificate.Execution
