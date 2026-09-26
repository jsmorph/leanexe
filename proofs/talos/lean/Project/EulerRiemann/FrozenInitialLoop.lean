import Project.EulerRiemann.FrozenInitialIteration

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.ProofKit

theorem initial_loop_spec (env : HostEnv Unit) (initial : Store Unit) (initialHeap : Heap)
    (n size limit pageLimit : Nat) (store : Store Unit) (frame : Locals)
    (hn : n ≤ 800) (hSize : size ≤ 640000) (hLimit : limit < 4294967296)
    (hCap : limit ≤ initial.memoryCap module 0 * 65536) (hPhysicalLimit : limit ≤ pageLimit * 65536)
    (hInv : initialInvariant initial initialHeap n size limit pageLimit store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame, initialExit initial initialHeap n size limit pageLimit final resultFrame →
      wp module rest Q final resultFrame env) :
    wp module ([.block 0 0 [.loop 0 0 initialLoop]] ++ rest) Q store frame env := by
  apply BlockLoop.program_spec module env store frame initialLoop
    (initialInvariant initial initialHeap n size limit pageLimit)
    (initialExit initial initialHeap n size limit pageLimit) (fun _ current => initialMeasure current)
    (fun _ _ h => h.values) (fun _ _ h => h.1.values) hInv
  · intro current currentFrame hCurrent
    exact initial_iteration_spec env initial initialHeap n size limit pageLimit current currentFrame
      hn hSize hLimit hCap hPhysicalLimit hCurrent
  · exact hNext

#print axioms initial_loop_spec

end Project.EulerRiemann.Frozen.Execution
