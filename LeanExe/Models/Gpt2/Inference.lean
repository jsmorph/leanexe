import LeanExe.Models.Gpt2.Block

namespace LeanExe.Models.Gpt2

def vocabulary : Nat := 50257
def positionOffset : Nat := vocabulary * 768
def blocksOffset : Nat := positionOffset + 1024 * 768
def finalNormOffset : Nat := blocksOffset + 12 * blockWords
def parameterWords : Nat := finalNormOffset + 1536

def validTokens (tokens : ByteArray) : Bool := Id.run do
  if tokens.size == 0 || tokens.size > 512 || tokens.size % 4 != 0 then return false
  for index in [:tokens.size / 4] do
    if (word tokens index).toNat ≥ vocabulary then return false
  return true

def embeddings (weights tokens : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (tokens.size / 4 * 768) fun index =>
    let token := (word tokens (index / 768)).toNat
    LeanExe.Float32.addBits (word weights (token * 768 + index % 768))
      (word weights (positionOffset + index))

def hiddenStates (weights tokens : ByteArray) : ByteArray := Id.run do
  let rows := tokens.size / 4
  let mut hidden := embeddings weights tokens
  for layer in [:12] do
    hidden := transformerBlock weights hidden (blocksOffset + layer * blockWords) rows
  return hidden

def vocabularyHead (weights hidden : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE vocabulary fun token => Id.run do
    let mut total : UInt32 := 0
    for channel in [:768] do
      total := LeanExe.Float32.addBits total
        (LeanExe.Float32.mulBits (word hidden channel) (word weights (token * 768 + channel)))
    return total

def infer (weights tokens : ByteArray) : ByteArray :=
  if weights.size != parameterWords * 4 || !validTokens tokens then ByteArray.empty
  else
    let hidden := hiddenStates weights tokens
    let last := hidden.extract (hidden.size - 768 * 4) hidden.size
    let normalized := layerNorm weights last finalNormOffset (finalNormOffset + 768) 1
    vocabularyHead weights normalized

end LeanExe.Models.Gpt2
