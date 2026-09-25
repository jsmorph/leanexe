import Project.Gpt2QuantizedCached.Session.Step

namespace Project.Gpt2QuantizedCached.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem runs_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (cache : ByteArray) (position : Nat) (initial : Store Unit) (heap : Heap)
    (weightNode cacheNode : FreeNode)
    (hReady : Ready weights cache position initial heap weightNode cacheNode)
    (hLength : position + tokens.length ≤ 128) :
    Runs env weightNode.root weights.size tokens position cacheNode.root cache.size initial
      (sourceTrace weights tokens cache position) := by
  induction tokens generalizing cache position initial heap cacheNode with
  | nil => exact ⟨rfl, hReady.close env⟩
  | cons token tokens ih =>
    simp only [List.length_cons] at hLength
    simp only [sourceTrace, Runs, RunsFor]
    apply (step env weights cache token position initial heap weightNode cacheNode hReady (by omega)
      (fun next => Runs env weightNode.root weights.size tokens (position + 1)
        (Entry.outputCacheNode heap weights cache token position).root (cachedStep weights cache token position).cache.size next
        (sourceTrace weights tokens (cachedStep weights cache token position).cache (position + 1))) ?_).mono
    · rintro final values ⟨hValues, hCache, hLogits, hRest⟩
      refine ⟨statusRoot (cachedStep weights cache token position).status (Entry.outputCacheNode heap weights cache token position),
        statusRoot (cachedStep weights cache token position).status (Entry.outputLogitsNode heap weights cache token position),
        hValues, hCache, hLogits, ?_⟩
      by_cases hZero : (cachedStep weights cache token position).status = 0
      · simpa only [hZero, statusRoot, ite_true] using hRest
      · simpa only [hZero, statusRoot, ite_false, true_and] using hRest
    · intro _ next nextHeap hNext
      exact ih _ _ next nextHeap _ hNext (by omega)

theorem initialized_runs_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (hWeights : weights.size = 127695972) (hLength : tokens.length ≤ 128) :
    Runs env Initialize.weightNode.root weights.size tokens 0 0 0 (Initialize.store weights)
      (sourceTrace weights tokens ByteArray.empty 0) :=
  runs_exact env weights tokens ByteArray.empty 0 (Initialize.store weights) Initialize.heap
    Initialize.weightNode ⟨0, 0⟩ (ready_initial weights hWeights) (by omega)

#print axioms runs_exact
#print axioms initialized_runs_exact
end Project.Gpt2QuantizedCached.Session
