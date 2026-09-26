import Project.Gpt2QuantizedCached.CachedBlock.Source
import Project.Gpt2QuantizedCached.Numerical.TensorBounds

namespace Project.Gpt2QuantizedCached.Numerical.Block
open LeanExe.Models.Gpt2 Project.ProofKit

abbrev Tensors := Gpt2QuantizedCached.CachedBlock.Tensors
abbrev quantizedTensors := Gpt2QuantizedCached.CachedBlock.tensors

def qBase (layer : Nat) : Nat := Quantized.blocksOffset + layer * Quantized.blockBytes
def rBase (layer : Nat) : Nat := blocksOffset + layer * blockWords

def qkvLayout (layer : Nat) : ProjectionPair.Layout :=
  ⟨qBase layer + Quantized.qkvWeightOffset, qBase layer + Quantized.qkvScaleOffset,
    qBase layer + Quantized.qkvBiasOffset, rBase layer + qkvWeightOffset, rBase layer + qkvBiasOffset, 768, 2304⟩
def attentionLayout (layer : Nat) : ProjectionPair.Layout :=
  ⟨qBase layer + Quantized.attnWeightOffset, qBase layer + Quantized.attnScaleOffset,
    qBase layer + Quantized.attnBiasOffset, rBase layer + attnWeightOffset, rBase layer + attnBiasOffset, 768, 768⟩
def expansionLayout (layer : Nat) : ProjectionPair.Layout :=
  ⟨qBase layer + Quantized.fcWeightOffset, qBase layer + Quantized.fcScaleOffset,
    qBase layer + Quantized.fcBiasOffset, rBase layer + fcWeightOffset, rBase layer + fcBiasOffset, 768, 3072⟩
def contractionLayout (layer : Nat) : ProjectionPair.Layout :=
  ⟨qBase layer + Quantized.mlpWeightOffset, qBase layer + Quantized.mlpScaleOffset,
    qBase layer + Quantized.mlpBiasOffset, rBase layer + mlpWeightOffset, rBase layer + mlpBiasOffset, 3072, 768⟩

def referenceTensors (weights input cache : ByteArray) (layer position : Nat) : Tensors :=
  let base := rBase layer
  let normalized := layerNorm weights input base (base + 768) 1
  let qkv := linearRows weights normalized (base + qkvWeightOffset) (base + qkvBiasOffset) 768 2304 1
  let mixed := cachedAttention cache qkv layer position
  let projected := linearRows weights mixed (base + attnWeightOffset) (base + attnBiasOffset) 768 768 1
  let residual := addRows input projected
  let normalized2 := layerNorm weights residual (base + ln2ScaleOffset) (base + ln2BiasOffset) 1
  let expanded := linearRows weights normalized2 (base + fcWeightOffset) (base + fcBiasOffset) 768 3072 1
  let activated := activate expanded
  let projected2 := linearRows weights activated (base + mlpWeightOffset) (base + mlpBiasOffset) 3072 768 1
  ⟨normalized, qkv, mixed, projected, residual, normalized2, expanded, activated, projected2, addRows residual projected2⟩

theorem reference_sizes (weights input cache : ByteArray) (layer position : Nat)
    (hInput : input.size = 3072) : (referenceTensors weights input cache layer position).Sizes := by
  constructor <;> simp only [referenceTensors, Gpt2CachedStep.LayerNorm.layerNorm_size,
    Gpt2CachedStep.CachedAttention.Spec.cachedAttention_size, linearRows, addRows, activate,
    PackedSource.generate_size, hInput]

theorem reference_hidden (weights input cache : ByteArray) (layer position : Nat) :
    (cachedBlock weights input cache layer position).hidden = (referenceTensors weights input cache layer position).hidden := rfl

theorem reference_cache (weights input cache : ByteArray) (layer position : Nat) :
    (cachedBlock weights input cache layer position).cache =
      Gpt2CachedStep.CachedBlock.cacheUpdate (referenceTensors weights input cache layer position).qkv := rfl

theorem quantized_hidden (weights input cache : ByteArray) (layer position : Nat)
    (h : (quantizedTensors weights input cache layer position).accepted = true) :
    (Quantized.cachedBlock weights input cache layer position).hidden =
      (quantizedTensors weights input cache layer position).hidden := by
  rw [Gpt2QuantizedCached.CachedBlock.cachedBlock_tensors]
  simp only [h, ite_true]

theorem quantized_cache (weights input cache : ByteArray) (layer position : Nat)
    (h : (quantizedTensors weights input cache layer position).accepted = true) :
    (Quantized.cachedBlock weights input cache layer position).cache =
      Gpt2CachedStep.CachedBlock.cacheUpdate (quantizedTensors weights input cache layer position).qkv := by
  rw [Gpt2QuantizedCached.CachedBlock.cachedBlock_tensors]
  simp only [h, ite_true]

#print axioms reference_sizes
#print axioms quantized_hidden
end Project.Gpt2QuantizedCached.Numerical.Block
