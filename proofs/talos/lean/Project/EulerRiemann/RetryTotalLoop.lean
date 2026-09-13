import Project.EulerRiemann.RetryTotalIteration

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayCapacity

theorem retry_total_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (source : FreeNode) (grid : Array Traversal.Cell) (n : Nat) (time : UInt64)
    (expected : Control.Attempt) (spare limit : Nat) (store : Store Unit) (frame : Locals)
    (hn : 2 ≤ n ∧ n ≤ 800) (hIndexed : Traversal.Indexed n grid)
    (hOwner : initialHeap.Owns initial source grid) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hInv : retryTotalInvariant initial initialHeap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final heap resultFrame,
      RetryStoreAt initial initialHeap final heap →
      RetryTotalStopped initial initialHeap n time source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit final heap resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 retryLoop]] ++ rest) Q store frame env := by
  refine Project.ProofKit.BlockLoop.program_spec module env store frame retryLoop
    (retryTotalInvariant initial initialHeap n time source.root
      (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit)
    (fun final resultFrame => ∃ heap, RetryStoreAt initial initialHeap final heap ∧
      RetryTotalStopped initial initialHeap n time source.root
        (normalizedCapacity (UInt64.ofNat grid.size) 7) grid expected spare limit final heap resultFrame)
    (fun _ current => retryMeasure current) (fun _ _ h => h.values) ?_ hInv ?_ Q rest ?_
  · intro final resultFrame ⟨heap, _, hDone⟩
    exact hDone.values
  · intro current currentFrame hCurrent
    exact retry_total_iteration_spec env initial initialHeap source grid n time expected
      spare limit current currentFrame hn hIndexed hOwner hLimit hCap hCurrent
  · intro final resultFrame ⟨heap, hStore, hDone⟩
    exact hNext final heap resultFrame hStore hDone

#print axioms retry_total_loop_spec

end Project.EulerRiemann.Execution
