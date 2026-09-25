import LeanExe.Models.Gpt2.Kernel
import LeanExe.Signed32

namespace LeanExe.Models.Gpt2.Quantized

def finite (value : UInt32) : Bool :=
  (value &&& 0x7FFFFFFF) < 0x7F800000

def finiteWords (bytes : ByteArray) (offset count : Nat) : Bool := Id.run do
  let mut valid := true
  for i in [:count] do
    valid := valid && finite (LeanExe.Packed.getUInt32LE! bytes (offset + i * 4))
  return valid

def rowScale (input : ByteArray) (offset width : Nat) : UInt32 := Id.run do
  let mut maximum : UInt32 := 0
  for i in [:width] do
    let magnitude := word input (offset + i) &&& 0x7FFFFFFF
    if maximum < magnitude then maximum := magnitude
  if maximum == 0 then return 0x3F800000
  let scale := LeanExe.Float32.divBits maximum 0x42FE0000
  return if scale < 0x00800000 then 0x00800000 else scale

def quantizeValue (value scale : UInt32) : UInt8 :=
  let quotient := LeanExe.Float32.divBits value scale
  let magnitude := quotient &&& 0x7FFFFFFF
  let clamped :=
    if magnitude > 0x42FE0000 then 0x42FE0000 ||| (quotient &&& 0x80000000)
    else quotient
  (LeanExe.Float32.toInt32Bits (LeanExe.Float32.nearestBits clamped)).toUInt8

structure Rows where
  values : ByteArray
  scales : ByteArray

def quantizeRows (input : ByteArray) (width rows : Nat) : Rows :=
  let scales := LeanExe.Packed.generateUInt32LE rows fun row => rowScale input (row * width) width
  let values := LeanExe.Packed.generateUInt8 (rows * width) fun index =>
    quantizeValue (word input index) (word scales (index / width))
  { values, scales }

def dot (weights input : ByteArray) (weightOffset inputOffset width : Nat) : UInt32 := Id.run do
  let mut accumulator : UInt32 := 0
  for i in [:width] do
    let x := LeanExe.Signed32.extend8Bits input[inputOffset + i]!.toUInt32
    let w := LeanExe.Signed32.extend8Bits weights[weightOffset + i]!.toUInt32
    accumulator := accumulator + x * w
  return accumulator

def rescale (accumulator inputScale weightScale : UInt32) : UInt32 :=
  let scale := LeanExe.Float32.mulBits inputScale weightScale
  LeanExe.Float32.mulBits (LeanExe.Float32.ofInt32Bits accumulator) scale

def linearRows (weights input : ByteArray) (weightOffset scaleOffset biasOffset : Nat)
    (inputWidth outputWidth rows : Nat) (withBias : Bool) : ByteArray :=
  let quantized := quantizeRows input inputWidth rows
  LeanExe.Packed.generateUInt32LE (rows * outputWidth) fun index =>
    let row := index / outputWidth
    let column := index % outputWidth
    let accumulator := dot weights quantized.values
      (weightOffset + column * inputWidth) (row * inputWidth) inputWidth
    let value := rescale accumulator (word quantized.scales row)
      (LeanExe.Packed.getUInt32LE! weights (scaleOffset + column * 4))
    if withBias then LeanExe.Float32.addBits value
      (LeanExe.Packed.getUInt32LE! weights (biasOffset + column * 4))
    else value

def validCoefficients (weights : ByteArray) (offset count : Nat) : Bool := Id.run do
  let mut valid := true
  for i in [:count] do
    valid := valid && weights[offset + i]! != 0x80
  return valid

def validScales (weights : ByteArray) (offset count : Nat) : Bool := Id.run do
  let mut valid := true
  for i in [:count] do
    let scale := LeanExe.Packed.getUInt32LE! weights (offset + i * 4)
    valid := valid && 0x00800000 ≤ scale && scale < 0x7F800000
  return valid

structure Result where
  status : UInt64
  output : ByteArray

def linearChecked (weights input : ByteArray) (weightOffset scaleOffset biasOffset : Nat)
    (inputWidth outputWidth rows : Nat) (withBias : Bool) : Result := Id.run do
  if inputWidth == 0 || inputWidth > 3072 || outputWidth == 0 || outputWidth > 50257 ||
      rows == 0 || rows > 128 || weights.size > 2147483648 ||
      weightOffset > weights.size || scaleOffset > weights.size || biasOffset > weights.size then
    return { status := 1, output := ByteArray.empty }
  if weightOffset + inputWidth * outputWidth > weights.size ||
      scaleOffset + outputWidth * 4 > weights.size ||
      (withBias && biasOffset + outputWidth * 4 > weights.size) ||
      input.size != rows * inputWidth * 4 then
    return { status := 1, output := ByteArray.empty }
  if !validCoefficients weights weightOffset (inputWidth * outputWidth) ||
      !validScales weights scaleOffset outputWidth ||
      (withBias && !finiteWords weights biasOffset outputWidth) then
    return { status := 2, output := ByteArray.empty }
  if !finiteWords input 0 (rows * inputWidth) then
    return { status := 3, output := ByteArray.empty }
  let output := linearRows weights input weightOffset scaleOffset biasOffset
    inputWidth outputWidth rows withBias
  if !finiteWords output 0 (rows * outputWidth) then
    return { status := 4, output := ByteArray.empty }
  return { status := 0, output }

end LeanExe.Models.Gpt2.Quantized
