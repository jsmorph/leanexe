import LeanExe.Models.Gpt2.Cached

namespace Project.Gpt2CachedStep.CachedAttention
open LeanExe.Models.Gpt2

def scores (cache qkv : ByteArray) (layer position : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (12 * (position + 1)) fun index =>
    cachedScore cache qkv layer position (index % (position + 1)) (index / (position + 1))

def maxima (scores : ByteArray) (size : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE 12 fun head => cachedRowMaximum scores head size

def exponentials (scores maxima : ByteArray) (size : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (12 * size) fun index =>
    expNeg (LeanExe.Float32.subBits (word scores index) (word maxima (index / size)))

def sums (exponentials : ByteArray) (size : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE 12 fun head => cachedRowSum exponentials head size

def probabilities (exponentials sums : ByteArray) (size : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (12 * size) fun index =>
    LeanExe.Float32.divBits (word exponentials index) (word sums (index / size))

def mixedPrefix (cache qkv probabilities : ByteArray) (layer position index count : Nat) : UInt32 :=
  (List.range count).foldl (fun total source =>
    LeanExe.Float32.addBits total
      (LeanExe.Float32.mulBits (word probabilities (index / 64 * (position + 1) + source))
        (cachedKv cache qkv layer position source (768 + index)))) 0

def mixed (cache qkv probabilities : ByteArray) (layer position : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE 768 fun index =>
    mixedPrefix cache qkv probabilities layer position index (position + 1)

end Project.Gpt2CachedStep.CachedAttention
