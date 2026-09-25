import LeanExe.Models.Gpt2.Quantized.Kernel

namespace LeanExe.Models.Gpt2.Quantized

def linearGroupedRows (weights input : ByteArray) (weightOffset scaleOffset biasOffset : Nat)
    (inputWidth outputWidth rows : Nat) (withBias : Bool) : ByteArray :=
  let groups := inputWidth / 64
  let quantized := quantizeRows input 64 (rows * groups)
  LeanExe.Packed.generateUInt32LE (rows * outputWidth) fun index =>
    let row := index / outputWidth
    let column := index % outputWidth
    let value := Id.run do
      let mut total : UInt32 := 0
      for group in [:groups] do
        let accumulator := dot weights quantized.values
          (weightOffset + column * inputWidth + group * 64) (row * inputWidth + group * 64) 64
        let partialValue := rescale accumulator (word quantized.scales (row * groups + group))
          (LeanExe.Packed.getUInt32LE! weights (scaleOffset + column * 4))
        total := LeanExe.Float32.addBits total partialValue
      return total
    if withBias then LeanExe.Float32.addBits value
      (LeanExe.Packed.getUInt32LE! weights (biasOffset + column * 4))
    else value

end LeanExe.Models.Gpt2.Quantized
