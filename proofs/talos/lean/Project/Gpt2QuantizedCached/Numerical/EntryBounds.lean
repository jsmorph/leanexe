import Project.Gpt2QuantizedCached.Numerical.HiddenResult
import Project.Gpt2QuantizedCached.Numerical.VocabularyPair
import Project.Gpt2QuantizedCached.Numerical.EntrySource

namespace Project.Gpt2QuantizedCached.Numerical.Entry
open LeanExe.Models.Gpt2

structure Parameters where
  hidden : Hidden.Parameters
  normalized : Norm.Parameters
  vocabulary : VocabularyPair.Parameters

def quantizedNormalized (qw qc : ByteArray) (token : UInt32) (position : Nat) : ByteArray :=
  layerNorm qw (Quantized.cachedHidden qw qc token position).hidden
    (Quantized.finalNormOffset / 4) (Quantized.finalNormOffset / 4 + 768) 1

def referenceNormalized (rw rc : ByteArray) (token : UInt32) (position : Nat) : ByteArray :=
  layerNorm rw (cachedHidden rw rc token position).hidden finalNormOffset (finalNormOffset + 768) 1

structure Ranges (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat) (p : Parameters) : Prop where
  hidden : Hidden.Ranges qw qc rw rc token position p.hidden
  normalized : Norm.Ranges qw (Quantized.cachedHidden qw qc token position).hidden
    rw (cachedHidden rw rc token position).hidden (Quantized.finalNormOffset / 4) (Quantized.finalNormOffset / 4 + 768)
      finalNormOffset (finalNormOffset + 768) p.normalized
  vocabulary : VocabularyPair.Ranges qw (quantizedNormalized qw qc token position)
    rw (referenceNormalized rw rc token position) p.vocabulary

noncomputable def normalizedError (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) : ℝ :=
  Norm.error qw (Quantized.cachedHidden qw qc token position).hidden rw (cachedHidden rw rc token position).hidden
    (Quantized.finalNormOffset / 4) finalNormOffset (Hidden.hiddenError qw qc rw rc token position cacheError p.hidden) p.normalized

noncomputable def logitError (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) (i : Nat) : ℝ :=
  VocabularyPair.componentError qw (quantizedNormalized qw qc token position) rw (referenceNormalized rw rc token position)
    (normalizedError qw qc rw rc token position cacheError p) p.vocabulary i

end Project.Gpt2QuantizedCached.Numerical.Entry
