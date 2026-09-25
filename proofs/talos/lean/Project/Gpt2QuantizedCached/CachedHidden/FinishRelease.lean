import Project.Gpt2QuantizedCached.CachedHidden.Completion
import Project.Gpt2QuantizedCached.CachedHidden.FinishResult
import Project.ProofKit.PackedReleaseFilter

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution

def finishUpdatesReleaseCode : Program :=
  PackedReleaseFilter.program 91 [13, 112, 115] [.localGet 91, .call 65]

def finishEmbeddingReleaseCode : Program :=
  PackedReleaseFilter.program 13 [112, 115] [.localGet 13, .call 65]

set_option maxRecDepth 32768 in
theorem emitted_finishRelease : (func58.drop 106).take 15 =
    finishUpdatesReleaseCode ++ finishEmbeddingReleaseCode := rfl

theorem finishRelease_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (status : UInt64) (hidden cache node : FreeNode) (hiddenBytes cacheBytes bytes : ByteArray)
    (frame : Locals) (ownerLocal : Nat) (retained : List (Nat × UInt64))
    (hMemory : Completion before original heap initial status hidden cache hiddenBytes cacheBytes)
    (hNode : heap.OwnsPacked initial node bytes) (hFresh : before.FreshNode node)
    (hHiddenSep : status = 0 → regionsDisjoint hidden.region node.region)
    (hCacheSep : status = 0 → regionsDisjoint cache.region node.region)
    (hValues : frame.values = []) (hRead : frame.get ownerLocal = some (.i64 node.root))
    (hRetained : ∀ entry ∈ retained, frame.get entry.1 = some (.i64 entry.2))
    (hDistinct : ∀ entry ∈ retained, node.root ≠ entry.2)
    (Q : Assertion Unit) (rest : Program)
    (hNext : Completion before original (heap.release node) (heap.releaseStore initial node)
      status hidden cache hiddenBytes cacheBytes → wp «module» rest Q (heap.releaseStore initial node) frame env) :
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
    exact hNext (hMemory.released node bytes hNode hFresh hHiddenSep hCacheSep hReleased)
  · intro hSkip
    apply False.elim
    apply hSkip
    refine ⟨?_, hDistinct⟩
    intro hZero
    have := hNode.buffer.rootBound
    rw [hZero] at this
    contradiction

#print axioms finishRelease_spec
end Project.Gpt2QuantizedCached.CachedHidden
