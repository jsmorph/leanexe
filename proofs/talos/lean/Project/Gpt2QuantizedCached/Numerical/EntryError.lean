import Project.Gpt2QuantizedCached.Numerical.EntryBounds

namespace Project.Gpt2QuantizedCached.Numerical.Entry
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

set_option maxRecDepth 8192

theorem normalized_error (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) (h : Ranges qw qc rw rc token position p)
    (hqc : qc.size = 4 * (position * 18432)) (hrc : rc.size = 4 * (position * 18432))
    (hc : Close qc rc (position * 18432) cacheError) :
    Close (quantizedNormalized qw qc token position) (referenceNormalized rw rc token position) 768
      (normalizedError qw qc rw rc token position cacheError p) := by
  have hh := Hidden.hidden_error qw qc rw rc token position cacheError p.hidden h.hidden hqc hrc hc
  exact Norm.close qw (Quantized.cachedHidden qw qc token position).hidden rw (cachedHidden rw rc token position).hidden
    (Quantized.finalNormOffset / 4) (Quantized.finalNormOffset / 4 + 768) finalNormOffset (finalNormOffset + 768)
    (Hidden.hiddenError qw qc rw rc token position cacheError p.hidden) p.normalized h.normalized hh.2.1

theorem step_error (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) (h : Ranges qw qc rw rc token position p)
    (hqc : qc.size = 4 * (position * 18432)) (hrc : rc.size = 4 * (position * 18432))
    (hc : Close qc rc (position * 18432) cacheError)
    (hSuccess : (Quantized.cachedStep qw qc token position).status = 0)
    (hw : rw.size = parameterWords * 4) (ht : token.toNat < vocabulary) (hp : position < 128) :
    Close (Quantized.cachedStep qw qc token position).cache (cachedStep rw rc token position).cache ((position + 1) * 18432)
      (Hidden.cacheBound qw qc rw rc token position cacheError p.hidden) ∧
      ∀ i < 50257,
        CodeLib.IEEE32.Finite (word (Quantized.cachedStep qw qc token position).logits i) ∧
        CodeLib.IEEE32.Finite (word (cachedStep rw rc token position).logits i) ∧
        |value (word (Quantized.cachedStep qw qc token position).logits i) -
          value (word (cachedStep rw rc token position).logits i)| ≤ logitError qw qc rw rc token position cacheError p i := by
  have hq := EntrySource.quantized_success qw qc token position hSuccess
  have hr := EntrySource.reference_success rw rc token position hw ht hp (by
    rw [hrc]
    unfold cachePositionWords
    omega)
  have hh := Hidden.hidden_error qw qc rw rc token position cacheError p.hidden h.hidden hqc hrc hc
  have hn := normalized_error qw qc rw rc token position cacheError p h hqc hrc hc
  constructor
  · rw [hq.1, hr.1]
    exact hh.2.2
  · intro i hi
    rw [hq.2, hr.2]
    exact VocabularyPair.component_error qw (quantizedNormalized qw qc token position) rw (referenceNormalized rw rc token position)
      (normalizedError qw qc rw rc token position cacheError p) p.vocabulary h.vocabulary hn i hi

#print axioms normalized_error
#print axioms step_error
end Project.Gpt2QuantizedCached.Numerical.Entry
