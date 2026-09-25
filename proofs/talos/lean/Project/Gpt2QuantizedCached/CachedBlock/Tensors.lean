import LeanExe.Models.Gpt2.Quantized.Cached
import Project.Gpt2CachedStep.LayerNorm.OutputSize
import Project.Gpt2CachedStep.CachedAttention.Spec
import Project.Gpt2CachedStep.CachedBlock.Source

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized Project.ProofKit

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
  let base := Quantized.blocksOffset + layer * blockBytes
  let normalized := layerNorm weights input (base / 4) (base / 4 + 768) 1
  let qkv := linearGroupedRows weights normalized (base + Quantized.qkvWeightOffset)
    (base + qkvScaleOffset) (base + Quantized.qkvBiasOffset) 768 2304 1 true
  let mixed := cachedAttention cache qkv layer position
  let projected := linearGroupedRows weights mixed (base + Quantized.attnWeightOffset)
    (base + attnScaleOffset) (base + Quantized.attnBiasOffset) 768 768 1 true
  let residual := addRows input projected
  let normalized2 := layerNorm weights residual ((base + Quantized.ln2ScaleOffset) / 4)
    ((base + Quantized.ln2BiasOffset) / 4) 1
  let expanded := linearGroupedRows weights normalized2 (base + Quantized.fcWeightOffset)
    (base + fcScaleOffset) (base + Quantized.fcBiasOffset) 768 3072 1 true
  let activated := activate expanded
  let projected2 := linearGroupedRows weights activated (base + Quantized.mlpWeightOffset)
    (base + mlpScaleOffset) (base + Quantized.mlpBiasOffset) 3072 768 1 true
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
    simp only [tensors, Gpt2CachedStep.LayerNorm.layerNorm_size,
      Gpt2CachedStep.CachedAttention.Spec.cachedAttention_size,
      linearGroupedRows, addRows, activate, PackedSource.generate_size, hInput]

def Tensors.accepted (values : Tensors) : Bool :=
  finiteWords values.normalized 0 768 && finiteWords values.mixed 0 768 &&
    finiteWords values.normalized2 0 768 && finiteWords values.activated 0 3072

#print axioms tensors_sizes
end Project.Gpt2QuantizedCached.CachedBlock
