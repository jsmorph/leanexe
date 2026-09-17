import LeanExe.Float32
import LeanExe.Packed

namespace LeanExe.Models.Gpt2

def linear (weights input : ByteArray) (weightOffset biasOffset : Nat)
    (inputWidth outputWidth : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE outputWidth fun column => Id.run do
    let mut sum : UInt32 := 0
    for row in [:inputWidth] do
      let x := LeanExe.Packed.getUInt32LE! input (row * 4)
      let w := LeanExe.Packed.getUInt32LE! weights (weightOffset + (row * outputWidth + column) * 4)
      sum := LeanExe.Float32.addBits sum (LeanExe.Float32.mulBits x w)
    return LeanExe.Float32.addBits sum (LeanExe.Packed.getUInt32LE! weights (biasOffset + column * 4))

end LeanExe.Models.Gpt2
