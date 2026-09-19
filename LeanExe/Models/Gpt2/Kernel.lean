import LeanExe.Float32
import LeanExe.Packed
import LeanExe.Models.Gpt2.Numerics

namespace LeanExe.Models.Gpt2

def word (bytes : ByteArray) (index : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! bytes (index * 4)

def linearRows (weights input : ByteArray) (weightOffset biasOffset : Nat)
    (inputWidth outputWidth rows : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (rows * outputWidth) fun index => Id.run do
    let row := index / outputWidth
    let column := index % outputWidth
    let mut sum : UInt32 := 0
    for i in [:inputWidth] do
      let x := word input (row * inputWidth + i)
      let w := word weights (weightOffset + i * outputWidth + column)
      sum := LeanExe.Float32.addBits sum (LeanExe.Float32.mulBits x w)
    return LeanExe.Float32.addBits sum (word weights (biasOffset + column))

def linear (weights input : ByteArray) (weightOffset biasOffset : Nat)
    (inputWidth outputWidth : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE outputWidth fun column => Id.run do
    let mut sum : UInt32 := 0
    for row in [:inputWidth] do
      let x := LeanExe.Packed.getUInt32LE! input (row * 4)
      let w := LeanExe.Packed.getUInt32LE! weights (weightOffset + (row * outputWidth + column) * 4)
      sum := LeanExe.Float32.addBits sum (LeanExe.Float32.mulBits x w)
    return LeanExe.Float32.addBits sum (LeanExe.Packed.getUInt32LE! weights (biasOffset + column * 4))

def rowMean (input : ByteArray) (row : Nat) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for i in [:768] do
    total := LeanExe.Float32.addBits total (word input (row * 768 + i))
  return LeanExe.Float32.divBits total 0x44400000

def rowInvStd (input : ByteArray) (row : Nat) (mean : UInt32) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for i in [:768] do
    let delta := LeanExe.Float32.subBits (word input (row * 768 + i)) mean
    total := LeanExe.Float32.addBits total (LeanExe.Float32.mulBits delta delta)
  let variance := LeanExe.Float32.divBits total 0x44400000
  let denominator := LeanExe.Float32.sqrtBits (LeanExe.Float32.addBits variance 0x3727C5AC)
  return LeanExe.Float32.divBits 0x3F800000 denominator

def layerNorm (weights input : ByteArray) (scaleOffset biasOffset rows : Nat) : ByteArray :=
  let means := LeanExe.Packed.generateUInt32LE rows fun row => rowMean input row
  let inverses := LeanExe.Packed.generateUInt32LE rows fun row => rowInvStd input row (word means row)
  LeanExe.Packed.generateUInt32LE (rows * 768) fun index =>
    let centered := LeanExe.Float32.subBits (word input index) (word means (index / 768))
    let normalized := LeanExe.Float32.mulBits centered (word inverses (index / 768))
    let scaled := LeanExe.Float32.mulBits normalized (word weights (scaleOffset + index % 768))
    LeanExe.Float32.addBits scaled (word weights (biasOffset + index % 768))

def attentionScore (qkv : ByteArray) (target source head : Nat) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for i in [:64] do
    let query := word qkv (target * 2304 + head * 64 + i)
    let key := word qkv (source * 2304 + 768 + head * 64 + i)
    total := LeanExe.Float32.addBits total (LeanExe.Float32.mulBits query key)
  return LeanExe.Float32.mulBits total 0x3E000000

def rowMaximum (scores : ByteArray) (row size : Nat) : UInt32 := Id.run do
  let mut maximum := word scores (row * size)
  for i in [:row / 12 + 1] do
    let value := word scores (row * size + i)
    if finiteLt maximum value then maximum := value
  return maximum

def rowSum (values : ByteArray) (row size : Nat) : UInt32 := Id.run do
  let mut total : UInt32 := 0
  for i in [:row / 12 + 1] do
    total := LeanExe.Float32.addBits total (word values (row * size + i))
  return total

def attention (qkv : ByteArray) (rows : Nat) : ByteArray :=
  let scores := LeanExe.Packed.generateUInt32LE (rows * 12 * rows) fun index =>
    let target := index / rows / 12
    let source := index % rows
    if source ≤ target then attentionScore qkv target source (index / rows % 12)
    else 0xFF800000
  let maxima := LeanExe.Packed.generateUInt32LE (rows * 12) fun row => rowMaximum scores row rows
  let exponentials := LeanExe.Packed.generateUInt32LE (rows * 12 * rows) fun index =>
    if index % rows ≤ index / rows / 12 then
      expNeg (LeanExe.Float32.subBits (word scores index) (word maxima (index / rows)))
    else 0
  let sums := LeanExe.Packed.generateUInt32LE (rows * 12) fun row => rowSum exponentials row rows
  let probabilities := LeanExe.Packed.generateUInt32LE (rows * 12 * rows) fun index =>
    LeanExe.Float32.divBits (word exponentials index) (word sums (index / rows))
  LeanExe.Packed.generateUInt32LE (rows * 768) fun index => Id.run do
    let target := index / 768
    let head := index % 768 / 64
    let channel := index % 64
    let mut total : UInt32 := 0
    for source in [:target + 1] do
      let probability := word probabilities ((target * 12 + head) * rows + source)
      let value := word qkv (source * 2304 + 1536 + head * 64 + channel)
      total := LeanExe.Float32.addBits total (LeanExe.Float32.mulBits probability value)
    return total

def addRows (left right : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (left.size / 4) fun index =>
    LeanExe.Float32.addBits (word left index) (word right index)

def activate (input : ByteArray) : ByteArray :=
  LeanExe.Packed.generateUInt32LE (input.size / 4) fun index => gelu (word input index)

end LeanExe.Models.Gpt2
