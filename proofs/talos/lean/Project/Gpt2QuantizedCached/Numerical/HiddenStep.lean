import Project.Gpt2QuantizedCached.Numerical.HiddenAdvance

namespace Project.Gpt2QuantizedCached.Numerical.Hidden
open LeanExe.Models.Gpt2 Project.ProofKit

set_option maxRecDepth 8192
set_option maxHeartbeats 30000

theorem step_bound (qw qc rw rc : ByteArray) (q : Gpt2QuantizedCached.CachedHidden.LayerState) (r : ByteArray × ByteArray)
    (layer position : Nat) (hl : layer < 12) (hiddenError updateError cacheError : ℝ) (p : Block.Parameters)
    (hp : StateBound q r layer hiddenError updateError)
    (h : Block.Ranges qw q.1 qc rw r.1 rc layer position (Block.quantizedTensors qw q.1 qc layer position)
      (Block.referenceTensors rw r.1 rc layer position) p)
    (accepted : (Block.quantizedTensors qw q.1 qc layer position).accepted = true)
    (hc : Close qc rc (position * 18432) cacheError) :
    StateBound (Gpt2QuantizedCached.CachedHidden.layerStep qw qc position q layer)
      (Gpt2CachedStep.CachedHidden.layerStep rw rc position r layer) (layer + 1)
      (nextErrors qw qc rw rc q.1 r.1 layer position hiddenError updateError cacheError p).1
      (nextErrors qw qc rw rc q.1 r.1 layer position hiddenError updateError cacheError p).2 := by
  let e := Block.errors qw q.1 qc rw r.1 rc layer position (Block.quantizedTensors qw q.1 qc layer position)
    (Block.referenceTensors rw r.1 rc layer position) hiddenError cacheError p
  have hqs := Gpt2QuantizedCached.CachedBlock.tensors_sizes qw q.1 qc layer position hp.hiddenSize
  have hqbHidden : (Quantized.cachedBlock qw q.1 qc layer position).hidden.size = 3072 := by
    rw [Block.quantized_hidden qw q.1 qc layer position accepted]
    exact hqs.hidden
  have hqbCache : (Quantized.cachedBlock qw q.1 qc layer position).cache.size = 6144 := by
    rw [Block.quantized_cache qw q.1 qc layer position accepted, Gpt2CachedStep.CachedBlock.cacheUpdate_size]
  have hqbStatus : (Quantized.cachedBlock qw q.1 qc layer position).status = 0 := by
    rw [Gpt2QuantizedCached.CachedBlock.cachedBlock_tensors]
    simp only [accepted, ite_true]
  have hBlock := Block.block_error qw q.1 qc rw r.1 rc layer position hl hp.hiddenSize hp.referenceHiddenSize
    hiddenError cacheError p h accepted hp.hiddenError hc
  have result := result_bound q r (Quantized.cachedBlock qw q.1 qc layer position)
    (cachedBlock rw r.1 rc layer position) layer hiddenError updateError e.hidden e.qkv hp hqbStatus hqbHidden hqbCache
    (Gpt2CachedStep.CachedBlock.Spec.cachedBlock_hidden_size _ _ _ _ _ hp.referenceHiddenSize)
    (Gpt2CachedStep.CachedBlock.Spec.cachedBlock_cache_size ..) hBlock.1 hBlock.2
  rw [Gpt2QuantizedCached.CachedHidden.layerStep_zero qw qc position layer q hp.status]
  exact result

#print axioms step_bound
end Project.Gpt2QuantizedCached.Numerical.Hidden
