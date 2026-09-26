import Project.Gpt2CachedStep.PointwiseError
import Project.Gpt2CachedStep.CachedBlock.Source

namespace Project.Gpt2QuantizedCached.Numerical.CacheError
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32
open Gpt2CachedStep.LayerNorm.Numerical (word_generate)

theorem lookup_error (qc qq rc rq : ByteArray) (layer position source offset : Nat)
    (hl : layer < 12) (ho : offset < 1536) (cacheError qkvError : ℝ)
    (hc : ∀ j < position * 18432, |value (word qc j) - value (word rc j)| ≤ cacheError)
    (hq : ∀ j < 2304, |value (word qq j) - value (word rq j)| ≤ qkvError) :
    |value (cachedKv qc qq layer position source offset) - value (cachedKv rc rq layer position source offset)| ≤
      max cacheError qkvError := by
  by_cases hs : source < position
  · simp only [cachedKv, ite_eq_left hs]
    exact (hc _ (by omega)).trans (le_max_left _ _)
  · simp only [cachedKv, ite_eq_right hs]
    exact (hq _ (by omega)).trans (le_max_right _ _)

theorem update_error (qq rq : ByteArray) (error : ℝ)
    (h : ∀ j < 2304, |value (word qq j) - value (word rq j)| ≤ error)
    (i : Nat) (hi : i < 1536) :
    |value (word (Gpt2CachedStep.CachedBlock.cacheUpdate qq) i) -
      value (word (Gpt2CachedStep.CachedBlock.cacheUpdate rq) i)| ≤ error := by
  simp only [Gpt2CachedStep.CachedBlock.cacheUpdate, word_generate 1536 _ i hi]
  exact h _ (by omega)

#print axioms lookup_error
#print axioms update_error
end Project.Gpt2QuantizedCached.Numerical.CacheError
