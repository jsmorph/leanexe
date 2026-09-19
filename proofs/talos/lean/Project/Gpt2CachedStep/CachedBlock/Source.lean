import LeanExe.Models.Gpt2.Cached
import Project.ProofKit.PackedSource

namespace Project.Gpt2CachedStep.CachedBlock
open LeanExe.Models.Gpt2

def cacheUpdate (qkv : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE 1536 fun index => word qkv (768 + index)

@[simp] theorem cacheUpdate_size (qkv : ByteArray) : (cacheUpdate qkv).size = 6144 :=
  Project.ProofKit.PackedSource.generate_size ..

theorem cachedBlock_eq (weights input cache : ByteArray) (layer position : Nat) :
    cachedBlock weights input cache layer position =
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
      { hidden := addRows residual projected2, cache := cacheUpdate qkv } := rfl

end Project.Gpt2CachedStep.CachedBlock
