import Project.Gpt2QuantizedCached.Entry.Public
import Project.Gpt2QuantizedCached.Entry.Sizes
import Project.Gpt2QuantizedCached.Entry.Budget
import Project.Gpt2QuantizedCached.Initialize

namespace Project.Gpt2QuantizedCached.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2.Quantized

def sourceTrace (weights : ByteArray) : List UInt32 → ByteArray → Nat → List CachedResult
  | [], _, _ => []
  | token :: tokens, cache, position =>
    let output := cachedStep weights cache token position
    output :: if output.status = 0 then sourceTrace weights tokens output.cache (position + 1) else []

def releaseThenFor (module_ : Wasm.Module) (env : HostEnv Unit) (pointer : UInt64) (store : Store Unit)
    (Q : Store Unit → Prop) : Prop :=
  if pointer = 0 then Q store else
    TerminatesWith env module_ 65 store [.i64 pointer] (fun final values => values = [] ∧ Q final)

def CloseFor (module_ : Wasm.Module) (env : HostEnv Unit) (weightPtr cachePtr : UInt64) (store : Store Unit) : Prop :=
  releaseThenFor module_ env cachePtr store (fun released =>
    TerminatesWith env module_ 65 released [.i64 weightPtr]
      (fun final values => values = [] ∧ final.mem.pages ≤ 65536))

def RunsFor (module_ : Wasm.Module) (env : HostEnv Unit) (weightsPtr : UInt64) (weightsSize : Nat) :
    List UInt32 → Nat → UInt64 → Nat → Store Unit → List CachedResult → Prop
  | [], _, cachePtr, _, initial, outputs => outputs = [] ∧ CloseFor module_ env weightsPtr cachePtr initial
  | _ :: _, _, _, _, _, [] => False
  | token :: tokens, position, cachePtr, cacheSize, initial, output :: outputs =>
    TerminatesWith env module_ 61 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64, .i64 (UInt64.ofNat cacheSize), .i64 cachePtr,
       .i64 (UInt64.ofNat weightsSize), .i64 weightsPtr]
      (fun final values => ∃ outputCachePtr outputLogitsPtr : UInt64,
        values = [.i64 (UInt64.ofNat output.logits.size), .i64 outputLogitsPtr,
          .i64 (UInt64.ofNat output.cache.size), .i64 outputCachePtr, .i64 output.status] ∧
        ByteArrayAt final.mem outputCachePtr.toNat output.cache ∧
        ByteArrayAt final.mem outputLogitsPtr.toNat output.logits ∧
        releaseThenFor module_ env cachePtr final (fun released =>
          releaseThenFor module_ env outputLogitsPtr released (fun next =>
            if output.status = 0 then
              RunsFor module_ env weightsPtr weightsSize tokens (position + 1) outputCachePtr output.cache.size next outputs
            else outputs = [] ∧ CloseFor module_ env weightsPtr outputCachePtr next)))

abbrev releaseThen := releaseThenFor «module»
abbrev Close := CloseFor «module»
abbrev Runs := RunsFor «module»

structure Ready (weights cache : ByteArray) (position : Nat) (store : Store Unit)
    (heap : Heap) (weightNode cacheNode : FreeNode) : Prop where
  heapAt : heap.At store
  weightOwner : heap.OwnsPacked store weightNode weights
  weightSize : weights.size = 127695972
  cacheSize : cache.size = position * 73728
  empty : position = 0 → cacheNode.root = 0
  cache : position ≠ 0 → heap.OwnsPacked store cacheNode cache
  separated : position ≠ 0 → regionsDisjoint weightNode.region cacheNode.region
  top : heap.top.toNat ≤ 134217728 + position * 16777216
  pages : store.mem.pages ≤ 65536
  capacity : store.memoryCap «module» 0 = 65536

theorem Ready.cache_at {weights cache : ByteArray} {position : Nat} {store : Store Unit}
    {heap : Heap} {weightNode cacheNode : FreeNode}
    (h : Ready weights cache position store heap weightNode cacheNode) :
    ByteArrayAt store.mem cacheNode.root.toNat cache := by
  by_cases hZero : position = 0
  · simp [ByteArrayAt, h.empty hZero, h.cacheSize, hZero]
  · exact (h.cache hZero).buffer.values

theorem Ready.cache_protected {weights cache : ByteArray} {position : Nat} {store : Store Unit}
    {heap : Heap} {weightNode cacheNode : FreeNode}
    (h : Ready weights cache position store heap weightNode cacheNode) :
    heap.Protects cacheNode.root.toNat (cacheNode.root.toNat + cache.size) := by
  by_cases hZero : position = 0
  · rw [h.empty hZero, h.cacheSize, hZero]
    exact ⟨Nat.zero_le _, fun _ _ => Or.inl (Nat.zero_le _)⟩
  · exact (h.cache hZero).payload_protects

theorem ready_initial (weights : ByteArray) (hSize : weights.size = 127695972) :
    Ready weights ByteArray.empty 0 (Initialize.store weights) Initialize.heap Initialize.weightNode ⟨0, 0⟩ := by
  obtain ⟨hHeap, hWeights, hPages, hCap, hTop⟩ := Initialize.input weights hSize
  exact ⟨hHeap, hWeights, hSize, rfl, fun _ => rfl, fun h => (h rfl).elim,
    fun h => (h rfl).elim, hTop, hPages, hCap⟩

#print axioms ready_initial

end Project.Gpt2QuantizedCached.Session
