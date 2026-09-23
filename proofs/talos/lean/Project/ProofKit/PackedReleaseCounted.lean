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

def enabled (owner : UInt64) (retained : List (Nat × UInt64)) : Bool :=
  owner != 0 && retained.all (fun entry => owner != entry.2)

theorem enabled_iff (owner : UInt64) (retained : List (Nat × UInt64)) :
    enabled owner retained = true ↔ owner ≠ 0 ∧ ∀ entry ∈ retained, owner ≠ entry.2 := by
  simp [enabled]

def filteredHeap (heap : Heap) (node : FreeNode) (owner : UInt64)
    (retained : List (Nat × UInt64)) : Heap :=
  if enabled owner retained then heap.release node else heap

def filteredStore (heap : Heap) (store : Store Unit) (node : FreeNode) (owner : UInt64)
    (retained : List (Nat × UInt64)) : Store Unit :=
  if enabled owner retained then heap.releaseStore store node else store

def filteredFrame (heap : Heap) (frame : Locals) (owner : UInt64)
    (retained : List (Nat × UInt64)) (scratch : Nat) : Locals :=
  if enabled owner retained then FixedArrayCapacity.capacityFrame frame scratch (heap.frees + 1)
  else frame

theorem filtered_spec (env : HostEnv Unit) (module_ : Wasm.Module) (releaseId : Nat)
    (initial : Store Unit) (heap : Heap) (frame : Locals) (node : FreeNode)
    (bytes : ByteArray) (owner : UInt64) (ownerLocal scratch : Nat)
    (retained : List (Nat × UInt64)) {typeIdx : Option Nat}
    (hFunction : module_.funcs[releaseId - module_.imports.length]? =
      some { releaseFuncDef releaseId with typeIdx := typeIdx })
    (hImport : module_.imports[releaseId]? = none) (hHeap : heap.At initial)
    (hOwner : enabled owner retained = true → owner = node.root ∧ heap.OwnsPacked initial node bytes)
    (hValues : frame.values = []) (hRead : frame.get ownerLocal = some (.i64 owner))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (hLower : frame.params.length ≤ scratch)
    (hUpper : scratch < frame.params.length + frame.locals.length)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : (filteredHeap heap node owner retained).At (filteredStore heap initial node owner retained) →
      wp module_ rest Q (filteredStore heap initial node owner retained)
        (filteredFrame heap frame owner retained scratch) env) :
    wp module_ (PackedReleaseFilter.program ownerLocal (retained.map Prod.fst)
      (program ownerLocal scratch releaseId) ++ rest) Q initial frame env := by
  apply PackedReleaseFilter.program_spec module_ env initial frame ownerLocal owner retained
    (program ownerLocal scratch releaseId) hValues hRead hRetained
  · intro hTaken
    have hEnabled := (enabled_iff owner retained).mpr hTaken
    obtain ⟨hRoot, hOwned⟩ := hOwner hEnabled
    have hRun := program_spec env module_ releaseId initial heap frame node bytes ownerLocal scratch
      hFunction hImport hHeap hOwned hValues (hRead.trans (congrArg (fun x => some (Value.i64 x)) hRoot))
      hLower hUpper (PackedReleaseFilter.afterAction module_ env rest Q) []
    apply (List.append_nil (program ownerLocal scratch releaseId)) ▸ hRun
    intro hReleased
    simpa only [filteredHeap, filteredStore, filteredFrame, hEnabled, ite_true, wp_nil,
      PackedReleaseFilter.afterAction, FixedArrayCapacity.capacityFrame] using hNext (by
        simpa only [filteredHeap, filteredStore, hEnabled, ite_true] using hReleased)
  · intro hSkip
    have hDisabled : enabled owner retained = false := by
      cases h : enabled owner retained
      · rfl
      · exact False.elim (hSkip ((enabled_iff owner retained).mp h))
    simpa only [filteredHeap, filteredStore, filteredFrame, hDisabled, Bool.false_eq_true, ite_false] using
      hNext (by simpa only [filteredHeap, filteredStore, hDisabled, Bool.false_eq_true, ite_false] using hHeap)

#print axioms filtered_spec
end Project.ProofKit.PackedReleaseCounted
