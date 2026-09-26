import Project.Gpt2QuantizedCached.Session.Close

namespace Project.Gpt2QuantizedCached.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem failure_continue (env : HostEnv Unit) (weights cache : ByteArray) (position : Nat)
    (initial final : Store Unit) (heap outputHeap : Heap) (weightNode oldCache newCache logits : FreeNode)
    (output : CachedResult) (hReady : Ready weights cache position initial heap weightNode oldCache)
    (hMemory : Entry.Completion heap initial outputHeap final output.status newCache logits output.cache output.logits)
    (hNonzero : output.status ≠ 0) :
    releaseThen env oldCache.root final (fun released =>
      releaseThen env (statusRoot output.status logits) released (fun next =>
        Close env weightNode.root (statusRoot output.status newCache) next)) := by
  have hWeights := hMemory.frame.ownsPacked hMemory.heapAt hReady.weightOwner
  have hClose := close_owned env final outputHeap weightNode oldCache weights cache hMemory.heapAt hWeights
    (fun hn => hMemory.frame.ownsPacked hMemory.heapAt (hReady.cache (fun hp => hn (hReady.empty hp))))
    (fun hn => hReady.separated (fun hp => hn (hReady.empty hp))) hMemory.pages
  simpa only [statusRoot, hNonzero, ite_false, releaseThen, releaseThenFor, Close, CloseFor,
    ite_true] using hClose

#print axioms failure_continue
end Project.Gpt2QuantizedCached.Session
