import LeanExe.Models.Gpt2.Quantized.Kernel

namespace LeanExe.Examples.QuantizedKernel
open LeanExe.Models.Gpt2

def projectionFP32 (weights input : ByteArray) (inputWidth outputWidth : Nat)
    (outputMajor withBias : Bool) : ByteArray :=
  LeanExe.Packed.generateUInt32LE outputWidth fun column => Id.run do
    let mut total : UInt32 := 0
    for i in [:inputWidth] do
      let index := if outputMajor then column * inputWidth + i else i * outputWidth + column
      total := LeanExe.Float32.addBits total
        (LeanExe.Float32.mulBits (word input i) (word weights index))
    return if withBias then LeanExe.Float32.addBits total
      (word weights (inputWidth * outputWidth + column)) else total

end LeanExe.Examples.QuantizedKernel
