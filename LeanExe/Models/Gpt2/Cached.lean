import LeanExe.Models.Gpt2.Inference

namespace LeanExe.Models.Gpt2

def cachePositionWords : Nat := 12 * 1536

def cachedKv (cache qkv : ByteArray) (layer position source offset : Nat) : UInt32 :=
  if source < position then word cache ((source * 12 + layer) * 1536 + offset)
  else word qkv (768 + offset)

def cachedScore (cache qkv : ByteArray) (layer position source head : Nat) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for channel in [:64] do
    let query := word qkv (head * 64 + channel)
    let key := cachedKv cache qkv layer position source (head * 64 + channel)
    total := LeanExe.Float32.addBits total (LeanExe.Float32.mulBits query key)
  return LeanExe.Float32.mulBits total 0x3E000000

def cachedRowMaximum (scores : ByteArray) (head size : Nat) : UInt32 := Id.run do
  let mut maximum := word scores (head * size)
  for source in [:size] do
    let value := word scores (head * size + source)
    if finiteLt maximum value then maximum := value
  return maximum

def cachedRowSum (values : ByteArray) (head size : Nat) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for source in [:size] do
    total := LeanExe.Float32.addBits total (word values (head * size + source))
  return total

def cachedAttention (cache qkv : ByteArray) (layer position : Nat) : ByteArray :=
  let size := position + 1
  let scores := LeanExe.Packed.generateUInt32LE (12 * size) fun index =>
    cachedScore cache qkv layer position (index % size) (index / size)
  let maxima := LeanExe.Packed.generateUInt32LE 12 fun head => cachedRowMaximum scores head size
  let exponentials := LeanExe.Packed.generateUInt32LE (12 * size) fun index =>
    expNeg (LeanExe.Float32.subBits (word scores index) (word maxima (index / size)))
  let sums := LeanExe.Packed.generateUInt32LE 12 fun head => cachedRowSum exponentials head size
  let probabilities := LeanExe.Packed.generateUInt32LE (12 * size) fun index =>
    LeanExe.Float32.divBits (word exponentials index) (word sums (index / size))
  LeanExe.Packed.generateUInt32LE 768 fun index => Id.run do
    let head := index / 64
    let mut total : UInt32 := 0
    for source in [:size] do
      let probability := word probabilities (head * size + source)
      let value := cachedKv cache qkv layer position source (768 + index)
      total := LeanExe.Float32.addBits total (LeanExe.Float32.mulBits probability value)
    return total

structure CachedHidden where
  hidden : ByteArray
  cache : ByteArray

def cachedBlock (weights input cache : ByteArray) (layer position : Nat) : CachedHidden :=
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
  { hidden := addRows residual projected2
    cache := LeanExe.Packed.generateUInt32LE 1536 fun index => word qkv (768 + index) }

def cachedHidden (weights cache : ByteArray) (token : UInt32) (position : Nat) : CachedHidden := Id.run do
  let mut hidden := LeanExe.Packed.generateUInt32LE 768 fun channel =>
    LeanExe.Float32.addBits (word weights (token.toNat * 768 + channel))
      (word weights (positionOffset + position * 768 + channel))
  let mut updates := ByteArray.empty
  for layer in [:12] do
    let result := cachedBlock weights hidden cache layer position
    hidden := result.hidden
    updates := updates ++ result.cache
  return { hidden, cache := cache ++ updates }

structure CachedResult where
  cache : ByteArray
  logits : ByteArray

def cachedStep (weights cache : ByteArray) (token : UInt32) (position : Nat) : CachedResult :=
  if weights.size != parameterWords * 4 || token.toNat ≥ vocabulary || position ≥ 128 ||
      cache.size != position * cachePositionWords * 4 then
    { cache := ByteArray.empty, logits := ByteArray.empty }
  else
    let result := cachedHidden weights cache token position
    let normalized := layerNorm weights result.hidden finalNormOffset (finalNormOffset + 768) 1
    { cache := result.cache, logits := vocabularyHead weights normalized }

end LeanExe.Models.Gpt2
