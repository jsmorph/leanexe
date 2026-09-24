import Project.Gpt2CachedStep.CachedBlock.FrozenSource
import Project.Gpt2CachedStep.LayerNorm.FrozenOutputSize
import Project.Gpt2CachedStep.CachedAttention.FrozenSpec

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open LeanExe.Models.Gpt2 Project.ProofKit

structure Tensors where
  normalized : ByteArray
  qkv : ByteArray
  mixed : ByteArray
  projected : ByteArray
  residual : ByteArray
  normalized2 : ByteArray
  expanded : ByteArray
  activated : ByteArray
  projected2 : ByteArray
  hidden : ByteArray

def tensors (weights input cache : ByteArray) (layer position : Nat) : Tensors :=
  let base := blocksOffset + layer * blockWords
  let normalized := layerNorm weights input base (base + 768) 1
  let qkv := linearRows weights normalized (base + qkvWeightOffset) (base + qkvBiasOffset) 768 2304 1
  let mixed := cachedAttention cache qkv layer position
  let projected := linearRows weights mixed (base + attnWeightOffset) (base + attnBiasOffset) 768 768 1
  let residual := addRows input projected
  let normalized2 := layerNorm weights residual (base + ln2ScaleOffset) (base + ln2BiasOffset) 1
  let expanded := linearRows weights normalized2 (base + fcWeightOffset) (base + fcBiasOffset) 768 3072 1
  let activated := activate expanded
  let projected2 := linearRows weights activated (base + mlpWeightOffset) (base + mlpBiasOffset) 3072 768 1
  let hidden := addRows residual projected2
  ⟨normalized, qkv, mixed, projected, residual, normalized2, expanded, activated, projected2, hidden⟩

structure Tensors.Sizes (values : Tensors) : Prop where
  normalized : values.normalized.size = 3072
  qkv : values.qkv.size = 9216
  mixed : values.mixed.size = 3072
  projected : values.projected.size = 3072
  residual : values.residual.size = 3072
  normalized2 : values.normalized2.size = 3072
  expanded : values.expanded.size = 12288
  activated : values.activated.size = 12288
  projected2 : values.projected2.size = 3072
  hidden : values.hidden.size = 3072

theorem tensors_sizes (weights input cache : ByteArray) (layer position : Nat)
    (hInput : input.size = 3072) : (tensors weights input cache layer position).Sizes := by
  constructor <;>
    simp only [tensors, LayerNorm.layerNorm_size, CachedAttention.Spec.cachedAttention_size,
      linearRows, addRows, activate, PackedSource.generate_size, hInput]

theorem cachedBlock_tensors (weights input cache : ByteArray) (layer position : Nat) :
    cachedBlock weights input cache layer position =
      { hidden := (tensors weights input cache layer position).hidden,
        cache := cacheUpdate (tensors weights input cache layer position).qkv } := rfl

#print axioms tensors_sizes

end Project.Gpt2CachedStep.Frozen.CachedBlock
