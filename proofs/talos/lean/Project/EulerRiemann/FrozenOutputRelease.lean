import Project.EulerRiemann.FrozenHeapWordsFinish
import Project.EulerRiemann.FrozenOutputHeaderExecute
import Interpreter.Wasm.Wp.Call

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold

def outputReleaseProgram (sourceLocal trackerLocal : Nat) : Wasm.Program :=
  [.localGet sourceLocal, .call 107, .globalGet 5, .localSet trackerLocal]

theorem output_release_shapes :
    (func99.drop 177).take 4 = outputReleaseProgram 13 28 ∧
    (func99.drop 181).take 4 = outputReleaseProgram 23 29 ∧
    (func99.drop 353).take 4 = outputReleaseProgram 26 33 := by
  exact ⟨rfl, rfl, rfl⟩

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

#print axioms output_release_shapes
#print axioms output_release_spec

end Project.EulerRiemann.Frozen.Execution
