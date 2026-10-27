import Verified.Bytes.Step
import Verified.RuntimeFacts
import LeanExe.Pipeline.ReleaseTree

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def releasedHeap (heap : Heap) (store : Store Unit) (root : UInt64) : Heap :=
  if root = 0 then heap else heap.release root (store.mem.read64 (root - 32).toUInt32)

def releasedStore (heap : Heap) (store : Store Unit) (root : UInt64) : Store Unit :=
  if root = 0 then store else heap.releaseStore store root

theorem Rep.release_step {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (hHeap : heap.At store) (h : Rep heap store root length bytes) :
    Step heap store (fun r => ∀ b ∈ regions store root, regionsDisjoint r b)
      (releasedHeap heap store root) (releasedStore heap store root) [] ∧
      (releasedHeap heap store root).top = heap.top := by
  rcases h.buffer with ⟨rfl, _⟩ | hBuffer
  · exact ⟨by simpa [releasedHeap, releasedStore] using
      Step.refl hHeap (fun r => ∀ b ∈ regions store 0, regionsDisjoint r b), rfl⟩
  · simp only [releasedHeap, releasedStore, ite_eq_right hBuffer.nonzero]
    refine ⟨⟨hHeap.release hBuffer.object, rfl, ?_⟩, rfl⟩
    intro r hRegion hPositive hApart
    exact Heap.Keeps.release hHeap hBuffer.object r hRegion hPositive fun b hb => by
      exact hApart b (by simpa only [regions, ite_eq_right hBuffer.nonzero] using hb)

theorem wp_release {m : Module} (hm : Runtime m) {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {root length : UInt64} {bytes : LeanExe.Bytes}
    {vs : List Value} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (h : Rep heap store root length bytes)
    (hNext : wp m rest Q (releasedStore heap store root) { s with values := vs } host) :
    wp m (.call 1 :: rest) Q store { s with values := .i64 root :: vs } host := by
  have hRun := ((h.release_run hm.imports hm.release host hHeap).runs
    (aborts := false)).append_args (by simp [hm.imports]) (by simpa [hm.imports] using hm.release)
    (by rfl) vs
  refine wp_call_runs hRun trivial fun st' out hPost => ?_
  obtain ⟨out', rfl, rfl, rfl⟩ := hPost
  exact hNext

end Verified.Bytes
