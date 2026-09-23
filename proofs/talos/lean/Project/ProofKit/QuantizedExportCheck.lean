import LeanExe.Models.Gpt2.Quantized.Kernel
import Interpreter.Wasm.IEEE32

namespace Project.ProofKit.QuantizedExport
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def roundedCoefficient (input scale : UInt32) : Int :=
  let clipped := (let quotient := Wasm.IEEE32.div input scale
    if (quotient &&& 0x7FFFFFFF) > 0x42FE0000 then 0x42FE0000 ||| (quotient &&& 0x80000000) else quotient)
  if Wasm.IEEE32.sign clipped then
    -(Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude clipped) 149 : Int)
  else Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude clipped) 149

def checkRow (source : ByteArray) (coefficients : ByteArray) (offset width : Nat)
    (scale : UInt32) : Bool :=
  source.size == width * 4 && offset + width ≤ coefficients.size &&
    scale == rowScale source 0 width && Wasm.IEEE32.isFinite scale &&
    decide (0 < Wasm.IEEE32.scaledValue scale) &&
    (List.range width).all (fun i =>
      Wasm.IEEE32.isFinite (word source i) && coefficients[offset + i]! != 128 &&
      decide (LeanExe.Signed32.decode (LeanExe.Signed32.extend8Bits coefficients[offset + i]!.toUInt32) =
        roundedCoefficient (word source i) scale) &&
      decide (Wasm.IEEE32.scaledMagnitude (word source i) * 2 ^ 149 ≤
        Wasm.IEEE32.scaledMagnitude scale * 2 ^ 156))

end Project.ProofKit.QuantizedExport
