import LeanExe.Models.Gpt2.Quantized.Cached

namespace Project.Gpt2QuantizedCached.Embedding.Error
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def coefficient (weights : ByteArray) (token : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Signed32.extend8Bits weights[tokenWeightOffset + token.toNat * 768 + i]!.toUInt32

def scale (weights : ByteArray) (token : UInt32) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (tokenScaleOffset + token.toNat * 4)

def positionWord (weights : ByteArray) (position i : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (Quantized.positionOffset + (position * 768 + i) * 4)

def reconstructed (weights : ByteArray) (token : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Float32.mulBits (LeanExe.Float32.ofInt32Bits (coefficient weights token i)) (scale weights token)

end Project.Gpt2QuantizedCached.Embedding.Error
