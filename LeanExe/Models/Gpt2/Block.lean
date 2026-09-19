import LeanExe.Models.Gpt2.Kernel

namespace LeanExe.Models.Gpt2

def qkvWeightOffset : Nat := 1536
def qkvBiasOffset : Nat := qkvWeightOffset + 768 * 2304
def attnWeightOffset : Nat := qkvBiasOffset + 2304
def attnBiasOffset : Nat := attnWeightOffset + 768 * 768
def ln2ScaleOffset : Nat := attnBiasOffset + 768
def ln2BiasOffset : Nat := ln2ScaleOffset + 768
def fcWeightOffset : Nat := ln2BiasOffset + 768
def fcBiasOffset : Nat := fcWeightOffset + 768 * 3072
def mlpWeightOffset : Nat := fcBiasOffset + 3072
def mlpBiasOffset : Nat := mlpWeightOffset + 3072 * 768
def blockWords : Nat := mlpBiasOffset + 768

def transformerBlock (weights input : ByteArray) (base rows : Nat) : ByteArray :=
  let normalized := layerNorm weights input base (base + 768) rows
  let qkv := linearRows weights normalized (base + qkvWeightOffset) (base + qkvBiasOffset) 768 2304 rows
  let mixed := attention qkv rows
  let projected := linearRows weights mixed (base + attnWeightOffset) (base + attnBiasOffset) 768 768 rows
  let residual := addRows input projected
  let normalized2 := layerNorm weights residual (base + ln2ScaleOffset) (base + ln2BiasOffset) rows
  let expanded := linearRows weights normalized2 (base + fcWeightOffset) (base + fcBiasOffset) 768 3072 rows
  let activated := activate expanded
  let projected2 := linearRows weights activated (base + mlpWeightOffset) (base + mlpBiasOffset) 3072 768 rows
  addRows residual projected2

end LeanExe.Models.Gpt2
