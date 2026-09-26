import Project.Gpt2QuantizedCached.Numerical.ForwardBlock
import Project.Gpt2QuantizedCached.Numerical.HiddenAdvance
import Project.Gpt2QuantizedCached.Numerical.HiddenFinish

namespace Project.Gpt2QuantizedCached.Numerical.ForwardUpper
open LeanExe.Models.Gpt2 Project.ProofKit

set_option maxRecDepth 8192

structure EmbeddingConditions (qw rw : ByteArray) (token : UInt32) (position : Nat) (d : StepData) : Prop where
  witness : ∃ p : EmbeddingPair.Parameters, EmbeddingPair.Ranges qw rw token position p ∧
    (∀ i < 768, p.qMul i = d.embeddingMul) ∧ (∀ i < 768, p.qAdd i = d.embeddingAdd) ∧
    (∀ i < 768, p.rAdd i = d.referenceEmbeddingAdd) ∧ (∀ i < 768, p.weightError i ≤ DyadicUpper.value d.embeddingWeightError)

structure HiddenConditions (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat) (d : StepData) : Prop where
  embedding : EmbeddingConditions qw rw token position d
  blocks : ∀ layer < 12,
    let qi := (Hidden.qState qw qc token position layer).1
    let ri := (Hidden.rState rw rc token position layer).1
    BlockConditions qw qi qc rw ri rc layer position (Block.quantizedTensors qw qi qc layer position)
      (Block.referenceTensors rw ri rc layer position) (d.blocks layer)
  accepted : ∀ layer < 12,
    (Block.quantizedTensors qw (Hidden.qState qw qc token position layer).1 qc layer position).accepted = true

theorem layer_step (qw qc rw rc : ByteArray) (q : Gpt2QuantizedCached.CachedHidden.LayerState) (r : ByteArray × ByteArray)
    (layer position E U C : Nat) (d : BlockData) (hl : layer < 12)
    (hp : Hidden.StateBound q r layer (DyadicUpper.value E) (DyadicUpper.value U))
    (h : BlockConditions qw q.1 qc rw r.1 rc layer position (Block.quantizedTensors qw q.1 qc layer position)
      (Block.referenceTensors rw r.1 rc layer position) d)
    (accepted : (Block.quantizedTensors qw q.1 qc layer position).accepted = true)
    (hc : Close qc rc (position * 18432) (DyadicUpper.value C)) :
    Hidden.StateBound (Gpt2QuantizedCached.CachedHidden.layerStep qw qc position q layer)
      (Gpt2CachedStep.CachedHidden.layerStep rw rc position r layer) (layer + 1)
      (DyadicUpper.value (block d position E C).hidden) (DyadicUpper.value (max U (block d position E C).qkv)) := by
  have hqs := Gpt2QuantizedCached.CachedBlock.tensors_sizes qw q.1 qc layer position hp.hiddenSize
  have hqbHidden : (Quantized.cachedBlock qw q.1 qc layer position).hidden.size = 3072 := by
    rw [Block.quantized_hidden qw q.1 qc layer position accepted]
    exact hqs.hidden
  have hqbCache : (Quantized.cachedBlock qw q.1 qc layer position).cache.size = 6144 := by
    rw [Block.quantized_cache qw q.1 qc layer position accepted, Gpt2CachedStep.CachedBlock.cacheUpdate_size]
  have hqbStatus : (Quantized.cachedBlock qw q.1 qc layer position).status = 0 := by
    rw [Gpt2QuantizedCached.CachedBlock.cachedBlock_tensors]
    simp only [accepted, ite_true]
  have hBlock := block_close qw q.1 qc rw r.1 rc layer position E C d hl hp.hiddenSize hp.referenceHiddenSize h hp.hiddenError hc
  have hh : Close (Quantized.cachedBlock qw q.1 qc layer position).hidden (cachedBlock rw r.1 rc layer position).hidden
      768 (DyadicUpper.value (block d position E C).hidden) := by
    rw [Block.quantized_hidden qw q.1 qc layer position accepted, Block.reference_hidden]
    exact hBlock.1
  have hu : Close (Quantized.cachedBlock qw q.1 qc layer position).cache (cachedBlock rw r.1 rc layer position).cache
      1536 (DyadicUpper.value (block d position E C).qkv) := by
    rw [Block.quantized_cache qw q.1 qc layer position accepted, Block.reference_cache]
    exact CacheError.update_error _ _ _ hBlock.2
  have result := Hidden.result_bound q r (Quantized.cachedBlock qw q.1 qc layer position)
    (cachedBlock rw r.1 rc layer position) layer (DyadicUpper.value E) (DyadicUpper.value U)
    (DyadicUpper.value (block d position E C).hidden) (DyadicUpper.value (block d position E C).qkv) hp hqbStatus hqbHidden hqbCache
    (Gpt2CachedStep.CachedBlock.Spec.cachedBlock_hidden_size _ _ _ _ _ hp.referenceHiddenSize)
    (Gpt2CachedStep.CachedBlock.Spec.cachedBlock_cache_size ..) hh hu
  rw [Gpt2QuantizedCached.CachedHidden.layerStep_zero qw qc position layer q hp.status, DyadicUpper.max_value]
  exact result

theorem layer_close (qw qc rw rc : ByteArray) (token : UInt32) (position C : Nat) (d : StepData)
    (h : HiddenConditions qw qc rw rc token position d) (hc : Close qc rc (position * 18432) (DyadicUpper.value C))
    (count : Nat) (hn : count ≤ 12) :
    Hidden.StateBound (Hidden.qState qw qc token position count) (Hidden.rState rw rc token position count) count
      (DyadicUpper.value (layerErrors d position C count).1) (DyadicUpper.value (layerErrors d position C count).2) := by
  induction count with
  | zero =>
    obtain ⟨p, hp, hm, ha, hr, hd⟩ := h.embedding.witness
    refine ⟨rfl, Gpt2QuantizedCached.CachedHidden.embedding_size qw token position, rfl,
      Gpt2CachedStep.CachedHidden.embedding_size rw token position, rfl,
      PointwiseUpper.embedding_close qw rw token position _ _ _ _ p hp hm ha hr hd, ?_⟩
    intro i hi
    omega
  | succ count ih =>
    have hp := ih (by omega)
    have hs := layer_step qw qc rw rc (Hidden.qState qw qc token position count) (Hidden.rState rw rc token position count)
      count position _ _ C (d.blocks count) (by omega) hp (h.blocks count (by omega)) (h.accepted count (by omega)) hc
    rw [Hidden.qState, Gpt2QuantizedCached.CachedHidden.layerPrefix_succ,
      Hidden.rState, Gpt2CachedStep.CachedHidden.layerPrefix_succ]
    exact hs

theorem hidden_close (qw qc rw rc : ByteArray) (token : UInt32) (position C : Nat) (d : StepData)
    (h : HiddenConditions qw qc rw rc token position d)
    (hqc : qc.size = 4 * (position * 18432)) (hrc : rc.size = 4 * (position * 18432))
    (hc : Close qc rc (position * 18432) (DyadicUpper.value C)) :
    (Quantized.cachedHidden qw qc token position).status = 0 ∧
      Close (Quantized.cachedHidden qw qc token position).hidden (cachedHidden rw rc token position).hidden 768
        (DyadicUpper.value (layerErrors d position C 12).1) ∧
      Close (Quantized.cachedHidden qw qc token position).cache (cachedHidden rw rc token position).cache ((position + 1) * 18432)
        (DyadicUpper.value (max C (layerErrors d position C 12).2)) := by
  have hp := layer_close qw qc rw rc token position C d h hc 12 (by decide)
  have hf := Hidden.finish_error qc rc (Hidden.qState qw qc token position 12) (Hidden.rState rw rc token position 12)
    position (DyadicUpper.value (layerErrors d position C 12).1) (DyadicUpper.value (layerErrors d position C 12).2)
    (DyadicUpper.value C) hp hqc hrc hc
  simpa only [Gpt2QuantizedCached.CachedHidden.cachedHidden_eq, Gpt2CachedStep.CachedHidden.cachedHidden_eq,
    Hidden.finishQuantized, Hidden.finishReference, Hidden.qState, Hidden.rState, DyadicUpper.max_value] using hf

#print axioms hidden_close
end Project.Gpt2QuantizedCached.Numerical.ForwardUpper
