import Project.EulerRiemann.AdvanceIteration
import Project.ProofKit.BlockLoop

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem advance_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n : Nat) (startTime : UInt64) (expected : Control.Result) (spare limit : Nat)
    (store : Store Unit) (frame : Locals) (hn : 2 ≤ n ∧ n ≤ 800)
    (hSuccess : expected.status = 0) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap Project.EulerRiemann.«module» 0 * 65536)
    (hInv : advanceInvariant initial initialHeap n startTime expected spare limit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final heap resultFrame,
      RetryStoreAt initial initialHeap final heap →
      AdvanceDone initial initialHeap n startTime expected spare limit final heap resultFrame →
      wp Project.EulerRiemann.«module» rest Q final resultFrame env) :
    wp Project.EulerRiemann.«module» ([.block 0 0 [.loop 0 0 advanceLoop]] ++ rest)
      Q store frame env := by
  refine Project.ProofKit.BlockLoop.program_spec _ env store frame advanceLoop
    (advanceInvariant initial initialHeap n startTime expected spare limit)
    (fun final resultFrame => ∃ heap, RetryStoreAt initial initialHeap final heap ∧
      AdvanceDone initial initialHeap n startTime expected spare limit final heap resultFrame)
    (fun _ current => advanceMeasure current) (fun _ _ h => h.values) ?_ hInv ?_ Q rest ?_
  · intro final resultFrame ⟨heap, hStore, hDone⟩
    exact (show advanceInvariant initial initialHeap n startTime expected spare limit final resultFrame
      from ⟨heap, hStore, Or.inr hDone⟩).values
  · intro current currentFrame hCurrent
    exact advance_iteration_spec env initial initialHeap n startTime expected spare limit
      current currentFrame hn hSuccess hLimit hCap hCurrent
  · intro final resultFrame ⟨heap, hStore, hDone⟩
    exact hNext final heap resultFrame hStore hDone

#print axioms advance_loop_spec

end Project.EulerRiemann.Execution
