import Project.EulerRiemann.HeapWordsFinish
import Project.EulerCertificate.SolverRegion
import Project.EulerReconstructed.RiemannRegion
import Project.ProofKit.FixedArrayFrame
import Interpreter.Wasm.Wp.Call

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold

theorem release_words_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (words : Array UInt64) (hHeap : heap.At initial)
    (hOwner : heap.OwnsWords initial node words) :
    TerminatesWith env module 194 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 152 (by norm_num [SolverRegion.domain])
    (Project.FunctionRegion.terminatesWith Project.EulerReconstructed.RiemannRegion.shift 107
      (by norm_num [Project.EulerReconstructed.RiemannRegion.domain])
      (Project.EulerRiemann.Execution.release_words_owned env initial heap node words hHeap hOwner))

def outputReleaseProgram (sourceLocal trackerLocal : Nat) : Wasm.Program :=
  [.localGet sourceLocal, .call 194, .globalGet 5, .localSet trackerLocal]


theorem output_release_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (frame : Locals) (node : FreeNode) (words : Array UInt64) (sourceLocal trackerLocal : Nat)
    (hHeap : heap.At store) (hOwner : heap.OwnsWords store node words)
    (hValues : frame.values = []) (hSource : frame.get sourceLocal = some (.i64 node.root))
    (hInternal : frame.params.length ≤ trackerLocal) (hValid : frame.validIndex trackerLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (heap.release node).At (heap.releaseStore store node) →
      wp module rest Q (heap.releaseStore store node) (resultFrame frame trackerLocal (heap.frees + 1)) env) :
    wp module (outputReleaseProgram sourceLocal trackerLocal ++ rest) Q store frame env := by
  simp only [outputReleaseProgram, List.cons_append, List.nil_append, wp_localGet_cons, hSource, hValues]
  refine wp_call_tw (release_words_owned env store heap node words hHeap hOwner) ?_
  rintro final values ⟨rfl, rfl, hFinalHeap⟩
  have hFrees : (heap.releaseStore store node).globals.globals[5]? = some (.i64 (heap.frees + 1)) := by
    rw [hFinalHeap.globals]
    rfl
  simp only [wp_globalGet_cons, hFrees, wp_localSet_cons]
  have hBound : trackerLocal < frame.params.length + frame.locals.length := hValid
  simpa [Locals.set?, resultFrame, Nat.not_lt.mpr hInternal, hBound] using hNext hFinalHeap

#print axioms release_words_owned
#print axioms output_release_spec

end Project.EulerCertificate.Execution
