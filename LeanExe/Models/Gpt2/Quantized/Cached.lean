import LeanExe.Models.Gpt2.Cached
import LeanExe.Models.Gpt2.Quantized.Format
import LeanExe.Models.Gpt2.Quantized.Grouped

namespace LeanExe.Models.Gpt2.Quantized

def embedding (weights : ByteArray) (token : UInt32) (position : Nat) : ByteArray :=
  let scale := LeanExe.Packed.getUInt32LE! weights (tokenScaleOffset + token.toNat * 4)
  LeanExe.Packed.generateUInt32LE 768 fun channel =>
    let coefficient := LeanExe.Signed32.extend8Bits
      weights[tokenWeightOffset + token.toNat * 768 + channel]!.toUInt32
    let value := LeanExe.Float32.mulBits (LeanExe.Float32.ofInt32Bits coefficient) scale
    LeanExe.Float32.addBits value
      (LeanExe.Packed.getUInt32LE! weights (positionOffset + (position * 768 + channel) * 4))

structure HiddenResult where
  status : UInt64
  hidden : ByteArray
  cache : ByteArray

def cachedBlock (weights input cache : ByteArray) (layer position : Nat) : HiddenResult :=
  let base := blocksOffset + layer * blockBytes
  let normalized := layerNorm weights input (base / 4) (base / 4 + 768) 1
  if !finiteWords normalized 0 768 then { status := 4, hidden := .empty, cache := .empty }
  else
    let qkv := linearGroupedRows weights normalized (base + qkvWeightOffset)
      (base + qkvScaleOffset) (base + qkvBiasOffset) 768 2304 1 true
    let mixed := cachedAttention cache qkv layer position
    if !finiteWords mixed 0 768 then { status := 4, hidden := .empty, cache := .empty }
    else
      let projected := linearGroupedRows weights mixed (base + attnWeightOffset)
        (base + attnScaleOffset) (base + attnBiasOffset) 768 768 1 true
      let residual := addRows input projected
      let normalized2 := layerNorm weights residual
        ((base + ln2ScaleOffset) / 4) ((base + ln2BiasOffset) / 4) 1
      if !finiteWords normalized2 0 768 then { status := 4, hidden := .empty, cache := .empty }
      else
        let expanded := linearGroupedRows weights normalized2 (base + fcWeightOffset)
          (base + fcScaleOffset) (base + fcBiasOffset) 768 3072 1 true
        let activated := activate expanded
        if !finiteWords activated 0 3072 then { status := 4, hidden := .empty, cache := .empty }
        else
          let projected2 := linearGroupedRows weights activated (base + mlpWeightOffset)
            (base + mlpScaleOffset) (base + mlpBiasOffset) 3072 768 1 true
          { status := 0
            hidden := addRows residual projected2
            cache := LeanExe.Packed.generateUInt32LE 1536 fun index => word qkv (768 + index) }

def cachedHidden (weights cache : ByteArray) (token : UInt32) (position : Nat) : HiddenResult := Id.run do
  let mut hidden := embedding weights token position
  let mut updates := ByteArray.empty
  let mut status : UInt64 := 0
  for layer in [:12] do
    if status == 0 then
      let result := cachedBlock weights hidden cache layer position
      status := result.status
      hidden := result.hidden
      updates := updates ++ result.cache
  if status != 0 then return { status, hidden := .empty, cache := .empty }
  return { status := 0, hidden, cache := cache ++ updates }

structure CachedResult where
  status : UInt64
  cache : ByteArray
  logits : ByteArray

def cachedStep (weights cache : ByteArray) (token : UInt32) (position : Nat) : CachedResult :=
  if !validHeader weights then { status := 1, cache := .empty, logits := .empty }
  else if token.toNat ≥ 50257 || position ≥ 128 ||
      cache.size != position * cachePositionWords * 4 then
    { status := 3, cache := .empty, logits := .empty }
  else if !finiteWords cache 0 (position * cachePositionWords) then
    { status := 3, cache := .empty, logits := .empty }
  else
    let result := cachedHidden weights cache token position
    if result.status != 0 then { status := result.status, cache := .empty, logits := .empty }
    else
      let normalized := layerNorm weights result.hidden (finalNormOffset / 4)
        (finalNormOffset / 4 + 768) 1
      if !finiteWords normalized 0 768 then { status := 4, cache := .empty, logits := .empty }
      else
        let logits := linearGroupedRows weights normalized tokenWeightOffset tokenScaleOffset 0 768 50257 1 false
        if !finiteWords result.cache 0 ((position + 1) * cachePositionWords) ||
            !finiteWords logits 0 50257 then { status := 4, cache := .empty, logits := .empty }
        else { status := 0, cache := result.cache, logits }

end LeanExe.Models.Gpt2.Quantized
