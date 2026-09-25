import Project.Gpt2QuantizedCached.Numerical.HiddenError
import Project.Gpt2QuantizedCached.Numerical.HiddenFinish

namespace Project.Gpt2QuantizedCached.Numerical.Hidden
open LeanExe.Models.Gpt2 Project.ProofKit

noncomputable def hiddenError (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) : ℝ := (layerErrors qw qc rw rc token position cacheError p 12).1

noncomputable def cacheBound (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) : ℝ := max cacheError (layerErrors qw qc rw rc token position cacheError p 12).2

theorem hidden_error (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) (h : Ranges qw qc rw rc token position p)
    (hqc : qc.size = 4 * (position * 18432)) (hrc : rc.size = 4 * (position * 18432))
    (hc : Close qc rc (position * 18432) cacheError) :
    (Quantized.cachedHidden qw qc token position).status = 0 ∧
      Close (Quantized.cachedHidden qw qc token position).hidden (cachedHidden rw rc token position).hidden 768
        (hiddenError qw qc rw rc token position cacheError p) ∧
      Close (Quantized.cachedHidden qw qc token position).cache (cachedHidden rw rc token position).cache ((position + 1) * 18432)
        (cacheBound qw qc rw rc token position cacheError p) := by
  have hp := prefix_error qw qc rw rc token position cacheError p h hc 12 (by decide)
  have hf := finish_error qc rc (qState qw qc token position 12) (rState rw rc token position 12)
    position (layerErrors qw qc rw rc token position cacheError p 12).1
      (layerErrors qw qc rw rc token position cacheError p 12).2 cacheError hp hqc hrc hc
  simpa only [Gpt2QuantizedCached.CachedHidden.cachedHidden_eq, Gpt2CachedStep.CachedHidden.cachedHidden_eq,
    finishQuantized, finishReference, hiddenError, cacheBound, qState, rState] using hf

#print axioms hidden_error
end Project.Gpt2QuantizedCached.Numerical.Hidden
