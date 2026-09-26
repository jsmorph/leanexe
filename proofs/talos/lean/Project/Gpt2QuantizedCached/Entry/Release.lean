import Project.Gpt2QuantizedCached.Entry.Completion
import Project.ProofKit.PackedReleaseFilter

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def releaseCode (owner : Nat) (retained : List Nat := [90, 93]) : Program :=
  PackedReleaseFilter.program owner retained [.localGet owner, .call 65]

theorem release_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (status : UInt64) (cache logits node : FreeNode) (cacheBytes logitsBytes bytes : ByteArray)
    (frame : Locals) (ownerLocal : Nat) (retained : List (Nat × UInt64))
    (hMemory : Completion before original heap initial status cache logits cacheBytes logitsBytes)
    (hNode : heap.OwnsPacked initial node bytes) (hFresh : before.FreshNode node)
    (hCacheSep : status = 0 → regionsDisjoint cache.region node.region)
    (hLogitsSep : status = 0 → regionsDisjoint logits.region node.region)
    (hValues : frame.values = []) (hRead : frame.get ownerLocal = some (.i64 node.root))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (hDistinct : ∀ entry ∈ retained, node.root ≠ entry.2)
    (Q : Assertion Unit) (rest : Program)
    (hNext : Completion before original (heap.release node) (heap.releaseStore initial node)
      status cache logits cacheBytes logitsBytes → wp «module» rest Q (heap.releaseStore initial node) frame env) :
    wp «module» (PackedReleaseFilter.program ownerLocal (retained.map Prod.fst)
      [.localGet ownerLocal, .call 65] ++ rest) Q initial frame env := by
  apply PackedReleaseFilter.program_spec «module» env initial frame ownerLocal node.root retained
    [.localGet ownerLocal, .call 65] hValues hRead hRetained
  · intro _
    simp only [Locals.get] at hRead
    wp_packed_frame [hValues, hRead]
    refine wp_call_tw (heap.releasePacked_exact env «module» 65 initial node bytes
      (typeIdx := some 65) rfl rfl hMemory.heapAt hNode) ?_
    rintro final returned ⟨rfl, rfl, hReleased⟩
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hEmpty : ({ frame with values := [] } : Locals) = frame := Frame.ext _ _ rfl rfl hValues.symm
    rw [hEmpty]
    exact hNext (hMemory.released node bytes hNode hFresh hCacheSep hLogitsSep hReleased)
  · intro hSkip
    apply False.elim
    apply hSkip
    refine ⟨?_, hDistinct⟩
    intro hZero
    have := hNode.buffer.rootBound
    rw [hZero] at this
    contradiction

#print axioms release_spec
end Project.Gpt2QuantizedCached.Entry
