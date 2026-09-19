import Project.Gpt2CachedStep.Session.Step

namespace Project.Gpt2CachedStep.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem runs_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (cache : ByteArray) (position : Nat) (initial : Store Unit) (heap : Heap)
    (weightNode cacheNode : FreeNode)
    (hReady : Ready weights cache position initial heap weightNode cacheNode)
    (hTokens : ∀ token ∈ tokens, token.toNat < 50257)
    (hLength : position + tokens.length ≤ 128) :
    Runs env weightNode.root weights.size tokens position cacheNode.root cache.size initial
      (sourceTrace weights tokens cache position) := by
  induction tokens generalizing cache position initial heap cacheNode with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.length_cons] at hLength
    simp only [sourceTrace, Runs, RunsFor]
    apply (step env weights cache token position initial heap weightNode cacheNode hReady
      (hTokens token (by simp)) (by omega)
      (fun next => Runs env weightNode.root weights.size tokens (position + 1)
        (Entry.cacheNode heap position cache.size).root (cachedStep weights cache token position).cache.size next
        (sourceTrace weights tokens (cachedStep weights cache token position).cache (position + 1))) ?_).mono
    · rintro final values ⟨hValues, hCache, hRest⟩
      exact ⟨(Entry.cacheNode heap position cache.size).root,
        (Entry.logitsNode heap position cache.size).root, hValues, hCache, hRest⟩
    · intro next nextHeap hNext
      exact ih _ _ next nextHeap _ hNext (fun t ht => hTokens t (List.mem_cons_of_mem _ ht)) (by omega)

theorem initialized_runs_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (hWeights : weights.size = 497759232)
    (hTokens : ∀ token ∈ tokens, token.toNat < 50257) (hLength : tokens.length ≤ 128) :
    Runs env Initialize.weightNode.root weights.size tokens 0 0 0 (Initialize.store weights)
      (sourceTrace weights tokens ByteArray.empty 0) :=
  runs_exact env weights tokens ByteArray.empty 0 (Initialize.store weights) Initialize.heap
    Initialize.weightNode ⟨0, 0⟩ (ready_initial weights hWeights) hTokens (by omega)

#print axioms runs_exact
#print axioms initialized_runs_exact

end Project.Gpt2CachedStep.Session

namespace Project.Gpt2CachedStep.Spec
open Wasm Project.ProofKit LeanExe.Models.Gpt2

theorem gpt2_128_exact (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32)
    (hWeights : weights.size = 497759232)
    (hTokens : ∀ token ∈ tokens, token.toNat < 50257) (hLength : tokens.length ≤ 128) :
    TerminatesWith env «module» 40 («module».initialStore (α := Unit)) []
      (fun reset returned => returned = [] ∧
        TerminatesWith env «module» 39 reset [.i64 Initialize.weightNeed]
      (fun allocated values => values = [.i64 Initialize.weightNode.root] ∧
        Session.Runs env Initialize.weightNode.root weights.size tokens 0 0 0
          (PackedInput.write allocated Initialize.weightNode.root.toNat weights)
          (Session.sourceTrace weights tokens ByteArray.empty 0))) := by
  apply (Initialize.reset_initial env).mono
  rintro reset returned ⟨rfl, rfl⟩
  refine ⟨rfl, ?_⟩
  apply (Initialize.allocate_exact env).mono
  rintro allocated values ⟨rfl, rfl⟩
  exact ⟨rfl, Session.initialized_runs_exact env weights tokens hWeights hTokens hLength⟩


def ExactSpecFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (weights : ByteArray) (tokens : List UInt32),
    weights.size = 497759232 →
    (∀ token ∈ tokens, token.toNat < 50257) → tokens.length ≤ 128 →
    TerminatesWith env module_ 40 (module_.initialStore (α := Unit)) []
      (fun reset returned => returned = [] ∧
        TerminatesWith env module_ 39 reset [.i64 Initialize.weightNeed]
      (fun allocated values => values = [.i64 Initialize.weightNode.root] ∧
        Session.RunsFor module_ env Initialize.weightNode.root weights.size tokens 0 0 0
          (PackedInput.write allocated Initialize.weightNode.root.toNat weights)
          (Session.sourceTrace weights tokens ByteArray.empty 0)))

theorem gpt2_128_exact_for : ExactSpecFor «module» := gpt2_128_exact

#print axioms gpt2_128_exact_for

#print axioms gpt2_128_exact

end Project.Gpt2CachedStep.Spec
