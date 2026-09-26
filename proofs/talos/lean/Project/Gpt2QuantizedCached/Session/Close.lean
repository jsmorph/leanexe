import Project.Gpt2QuantizedCached.Session.State
import Project.Gpt2QuantizedCached.Release

namespace Project.Gpt2QuantizedCached.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem close_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightNode cacheNode : FreeNode) (weights cache : ByteArray)
    (hHeap : heap.At initial) (hWeights : heap.OwnsPacked initial weightNode weights)
    (hCache : cacheNode.root ≠ 0 → heap.OwnsPacked initial cacheNode cache)
    (hSeparated : cacheNode.root ≠ 0 → regionsDisjoint weightNode.region cacheNode.region)
    (hPages : initial.mem.pages ≤ 65536) : Close env weightNode.root cacheNode.root initial := by
  have hFinish (store : Store Unit) (currentHeap : Heap)
      (hAt : currentHeap.At store) (hW : currentHeap.OwnsPacked store weightNode weights)
      (hP : store.mem.pages ≤ 65536) :
      TerminatesWith env «module» 65 store [.i64 weightNode.root]
        (fun final values => values = [] ∧ final.mem.pages ≤ 65536) := by
    apply (Release.release_owned env store currentHeap weightNode weights hAt hW).mono
    rintro final values ⟨rfl, rfl, _⟩
    exact ⟨rfl, hP⟩
  unfold Close CloseFor releaseThenFor
  split
  · exact hFinish initial heap hHeap hWeights hPages
  · rename_i hNonzero
    have hOwned := hCache hNonzero
    apply (Release.release_owned env initial heap cacheNode cache hHeap hOwned).mono
    rintro final values ⟨rfl, rfl, hReleased⟩
    exact ⟨rfl, hFinish _ (heap.release cacheNode) hReleased
      (hWeights.released cacheNode hOwned.buffer.rootBound (by have := hOwned.buffer.addressBound; omega)
        (hSeparated hNonzero)) hPages⟩

theorem Ready.close {weights cache : ByteArray} {position : Nat} {initial : Store Unit}
    {heap : Heap} {weightNode cacheNode : FreeNode}
    (h : Ready weights cache position initial heap weightNode cacheNode) (env : HostEnv Unit) :
    Close env weightNode.root cacheNode.root initial :=
  close_owned env initial heap weightNode cacheNode weights cache h.heapAt h.weightOwner
    (fun hn => h.cache (fun hp => hn (h.empty hp)))
    (fun hn => h.separated (fun hp => hn (h.empty hp))) h.pages

#print axioms close_owned
#print axioms Ready.close
end Project.Gpt2QuantizedCached.Session
