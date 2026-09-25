import Project.Gpt2QuantizedCached.Numerical.HiddenStep

namespace Project.Gpt2QuantizedCached.Numerical.Hidden
open LeanExe.Models.Gpt2 Project.ProofKit

theorem prefix_error (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) (h : Ranges qw qc rw rc token position p)
    (hc : Close qc rc (position * 18432) cacheError) (count : Nat) (hn : count ≤ 12) :
    PrefixBound qw qc rw rc token position count cacheError p := by
  induction count with
  | zero =>
    refine ⟨rfl, Gpt2QuantizedCached.CachedHidden.embedding_size qw token position, rfl,
      Gpt2CachedStep.CachedHidden.embedding_size rw token position, rfl,
      EmbeddingPair.close qw rw token position p.embedding h.embedding, ?_⟩
    intro i hi
    omega
  | succ count ih =>
    have hp := ih (by omega)
    have hs := step_bound qw qc rw rc (qState qw qc token position count) (rState rw rc token position count)
      count position (by omega) _ _ cacheError (p.block count) hp (h.blocks count (by omega)) (h.accepted count (by omega)) hc
    unfold PrefixBound
    rw [qState, Gpt2QuantizedCached.CachedHidden.layerPrefix_succ,
      rState, Gpt2CachedStep.CachedHidden.layerPrefix_succ]
    exact hs

#print axioms prefix_error
end Project.Gpt2QuantizedCached.Numerical.Hidden
