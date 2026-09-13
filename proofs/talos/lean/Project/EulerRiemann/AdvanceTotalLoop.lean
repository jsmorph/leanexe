import Project.EulerRiemann.AdvanceTotalIteration

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

theorem advance_total_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (startTime : UInt64) (expected : Control.Result) (spare limit : Nat)
    (store : Store Unit) (frame : Locals) (hn : 2 ≤ n ∧ n ≤ 800)
    (hLimit : limit < 4294967296) (hCap : limit ≤ initial.memoryCap module 0 * 65536)
    (hInv : advanceTotalInvariant initial initialHeap n startTime expected spare limit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final heap resultFrame,
      RetryStoreAt initial initialHeap final heap →
      AdvanceTotalDone initial initialHeap n startTime expected spare limit final heap resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 advanceLoop]] ++ rest) Q store frame env := by
  refine BlockLoop.program_spec module env store frame advanceLoop
    (advanceTotalInvariant initial initialHeap n startTime expected spare limit)
    (fun final resultFrame => ∃ heap, RetryStoreAt initial initialHeap final heap ∧
      AdvanceTotalDone initial initialHeap n startTime expected spare limit final heap resultFrame)
    (fun _ current => advanceMeasure current) (fun _ _ h => h.values) ?_ hInv ?_ Q rest ?_
  · intro final resultFrame ⟨heap, _, source, tracked, hFrame, _⟩
    exact hFrame.values
  · intro current currentFrame hCurrent
    exact advance_total_iteration_spec env initial initialHeap n startTime expected spare limit
      current currentFrame hn hLimit hCap hCurrent
  · intro final resultFrame ⟨heap, hStore, hDone⟩
    exact hNext final heap resultFrame hStore hDone

#print axioms advance_total_loop_spec

end Project.EulerRiemann.Execution
