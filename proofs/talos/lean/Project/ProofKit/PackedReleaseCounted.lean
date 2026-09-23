import Project.ProofKit.PackedAllocationState
import Project.ProofKit.PackedReleaseFilter

namespace Project.ProofKit.PackedReleaseCounted
open Wasm Project.Runtime Project.EulerRiemann.Execution PackedFloatFrame

def program (ownerLocal scratch releaseId : Nat) : Wasm.Program :=
  [.localGet ownerLocal, .call releaseId, .globalGet 5, .localSet scratch]

theorem program_spec (env : HostEnv Unit) (module_ : Wasm.Module) (releaseId : Nat)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (node : FreeNode)
    (bytes : ByteArray) (ownerLocal scratch : Nat) {typeIdx : Option Nat}
    (hFunction : module_.funcs[releaseId - module_.imports.length]? =
      some { releaseFuncDef releaseId with typeIdx := typeIdx })
    (hImport : module_.imports[releaseId]? = none)
    (hHeap : heap.At initial) (hOwner : heap.OwnsPacked initial node bytes)
    (hValues : frame.values = []) (hRead : frame.get ownerLocal = some (.i64 node.root))
    (hLower : frame.params.length ≤ scratch)
    (hUpper : scratch < frame.params.length + frame.locals.length)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (heap.release node).At (heap.releaseStore initial node) →
      wp module_ rest Q (heap.releaseStore initial node)
        (FixedArrayCapacity.capacityFrame frame scratch (heap.frees + 1)) env) :
    wp module_ (program ownerLocal scratch releaseId ++ rest) Q initial frame env := by
  simp only [program, List.cons_append, List.nil_append]
  have hRead' := hRead
  simp only [Locals.get] at hRead'
  wp_packed_frame [hValues, hRead']
  refine wp_call_tw (heap.releasePacked_exact env module_ releaseId initial node bytes
    hFunction hImport hHeap hOwner) ?_
  rintro final values ⟨rfl, rfl, hReleased⟩
  have hFrees : (heap.releaseStore initial node).globals.globals[5]? = some (.i64 (heap.frees + 1)) := by
    rw [hReleased.globals]
    rfl
  simp only [wp_globalGet_cons, hFrees]
  apply FixedArrayCapacity.storeWord_spec module_ env _
    { frame with values := [.i64 (heap.frees + 1)] } scratch (heap.frees + 1)
    hLower hUpper rfl
  exact hNext hReleased

#print axioms program_spec
end Project.ProofKit.PackedReleaseCounted
