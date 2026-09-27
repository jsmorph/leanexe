import LeanExe.Models.Gpt2.Numerics

namespace Project.Gpt2CachedStep.CachedAttention.SoftmaxError
open LeanExe.Models.Gpt2

def shifted (scores : Nat → UInt32) (maximum : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Float32.subBits (scores i) maximum

def exponential (scores : Nat → UInt32) (maximum : UInt32) (i : Nat) : UInt32 :=
  expNeg (shifted scores maximum i)

def denominator (scores : Nat → UInt32) (maximum : UInt32) (n : Nat) : UInt32 :=
  (List.range n).foldl (fun total i => LeanExe.Float32.addBits total (exponential scores maximum i)) 0

def probability (scores : Nat → UInt32) (maximum : UInt32) (n i : Nat) : UInt32 :=
  LeanExe.Float32.divBits (exponential scores maximum i) (denominator scores maximum n)

end Project.Gpt2CachedStep.CachedAttention.SoftmaxError
