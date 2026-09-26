import LeanExe.Models.Gpt2.Quantized.Kernel

namespace LeanExe.Models.Gpt2.Quantized

def headerBytes : Nat := 32
def tokenWeightOffset : Nat := headerBytes
def tokenScaleOffset : Nat := tokenWeightOffset + 50257 * 768
def positionOffset : Nat := tokenScaleOffset + 50257 * 4
def blocksOffset : Nat := positionOffset + 1024 * 768 * 4

def qkvWeightOffset : Nat := 1536 * 4
def qkvScaleOffset : Nat := qkvWeightOffset + 768 * 2304
def qkvBiasOffset : Nat := qkvScaleOffset + 2304 * 4
def attnWeightOffset : Nat := qkvBiasOffset + 2304 * 4
def attnScaleOffset : Nat := attnWeightOffset + 768 * 768
def attnBiasOffset : Nat := attnScaleOffset + 768 * 4
def ln2ScaleOffset : Nat := attnBiasOffset + 768 * 4
def ln2BiasOffset : Nat := ln2ScaleOffset + 768 * 4
def fcWeightOffset : Nat := ln2BiasOffset + 768 * 4
def fcScaleOffset : Nat := fcWeightOffset + 768 * 3072
def fcBiasOffset : Nat := fcScaleOffset + 3072 * 4
def mlpWeightOffset : Nat := fcBiasOffset + 3072 * 4
def mlpScaleOffset : Nat := mlpWeightOffset + 3072 * 768
def mlpBiasOffset : Nat := mlpScaleOffset + 768 * 4
def blockBytes : Nat := mlpBiasOffset + 768 * 4
def finalNormOffset : Nat := blocksOffset + 12 * blockBytes
def modelBytes : Nat := finalNormOffset + 1536 * 4

def validHeader (weights : ByteArray) : Bool :=
  weights.size == modelBytes &&
    LeanExe.Packed.getUInt32LE! weights 0 == 0x4751584C &&
    LeanExe.Packed.getUInt32LE! weights 4 == 0x00325450 &&
    LeanExe.Packed.getUInt32LE! weights 8 == 1 &&
    LeanExe.Packed.getUInt32LE! weights 12 == 32 &&
    LeanExe.Packed.getUInt32LE! weights 16 == 127695940 &&
    LeanExe.Packed.getUInt32LE! weights 20 == 2 &&
    LeanExe.Packed.getUInt32LE! weights 24 == 128 &&
    LeanExe.Packed.getUInt32LE! weights 28 == 0

def validBlock (weights : ByteArray) (base : Nat) : Bool :=
  finiteWords weights base 1536 &&
    validCoefficients weights (base + qkvWeightOffset) (768 * 2304) &&
    validScales weights (base + qkvScaleOffset) 2304 &&
    finiteWords weights (base + qkvBiasOffset) 2304 &&
    validCoefficients weights (base + attnWeightOffset) (768 * 768) &&
    validScales weights (base + attnScaleOffset) 768 &&
    finiteWords weights (base + attnBiasOffset) (768 * 3) &&
    validCoefficients weights (base + fcWeightOffset) (768 * 3072) &&
    validScales weights (base + fcScaleOffset) 3072 &&
    finiteWords weights (base + fcBiasOffset) 3072 &&
    validCoefficients weights (base + mlpWeightOffset) (3072 * 768) &&
    validScales weights (base + mlpScaleOffset) 768 &&
    finiteWords weights (base + mlpBiasOffset) 768

def validateModel (weights : ByteArray) : UInt64 := Id.run do
  if !validHeader weights then return 1
  if !validCoefficients weights tokenWeightOffset (50257 * 768) ||
      !validScales weights tokenScaleOffset 50257 ||
      !finiteWords weights positionOffset (1024 * 768) ||
      !finiteWords weights finalNormOffset 1536 then return 2
  for layer in [:12] do
    if !validBlock weights (blocksOffset + layer * blockBytes) then return 2
  return 0

end LeanExe.Models.Gpt2.Quantized
