import Project.Gpt2QuantizedCached.ExportCheck
import Project.ProofKit.F32UniformRangeCheck
import LeanExe.Models.Gpt2.Quantized.Kernel

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit

structure Layout where
  matrix : Export.Projection
  referenceBias : Nat
  quantizedBias : Nat
  withBias : Bool
  deriving Inhabited

def layouts : Array Layout := Id.run do
  let matrices := Export.projections.toArray
  let mut result := #[]
  for layer in [:12] do
    let rb := blocksOffset + layer * blockWords
    let qb := Quantized.blocksOffset + layer * Quantized.blockBytes
    let rBias := #[qkvBiasOffset, attnBiasOffset, fcBiasOffset, mlpBiasOffset]
    let qBias := #[Quantized.qkvBiasOffset, Quantized.attnBiasOffset, Quantized.fcBiasOffset, Quantized.mlpBiasOffset]
    for index in [:4] do
      result := result.push ⟨matrices[1 + layer * 4 + index]!, rb + rBias[index]!, qb + qBias[index]!, true⟩
  return result.push ⟨matrices[0]!, 0, 0, false⟩

def weightWord (weights : ByteArray) (p : Layout) (row column : Nat) : UInt32 :=
  word weights (p.matrix.sourceOffset + row * p.matrix.rowStride + column * p.matrix.columnStride)

def weightScale (weights : ByteArray) (p : Layout) (row : Nat) : UInt32 :=
  LeanExe.Packed.getUInt32LE! weights (p.matrix.scaleOffset + row * 4)

def magnitudeSum (input : Nat → UInt32) (count : Nat) : Nat :=
  (List.range count).foldl (fun total i => total + Wasm.IEEE32.scaledMagnitude (input i)) 0

structure WeightBounds where
  magnitude : Nat
  rowSum : Nat
  scaleMagnitude : Nat
  biasMagnitude : Nat
  deriving Inhabited

def profileWeights (reference quantized : ByteArray) (p : Layout) : WeightBounds := Id.run do
  let mut magnitude := 0
  let mut rowSum := 0
  let mut scaleMagnitude := 0
  let mut biasMagnitude := 0
  for row in [:p.matrix.outputWidth] do
    let mut total := 0
    for column in [:p.matrix.inputWidth] do
      let current := Wasm.IEEE32.scaledMagnitude (weightWord reference p row column)
      magnitude := max magnitude current
      total := total + current
    rowSum := max rowSum total
    scaleMagnitude := max scaleMagnitude (Wasm.IEEE32.scaledMagnitude (weightScale quantized p row))
    if p.withBias then
      biasMagnitude := max biasMagnitude (Wasm.IEEE32.scaledMagnitude (word reference (p.referenceBias + row)))
  return ⟨magnitude, rowSum, scaleMagnitude, biasMagnitude⟩

def checkWeights (reference quantized : ByteArray) (p : Layout) (b : WeightBounds) : Bool :=
  (List.range p.matrix.outputWidth).all fun row =>
    Wasm.IEEE32.isFinite (weightScale quantized p row) &&
    decide (Wasm.IEEE32.scaledMagnitude (weightScale quantized p row) ≤ b.scaleMagnitude) &&
    decide (magnitudeSum (weightWord reference p row) p.matrix.inputWidth ≤ b.rowSum) &&
    (List.range p.matrix.inputWidth).all (fun column =>
      Wasm.IEEE32.isFinite (weightWord reference p row column) &&
      decide (Wasm.IEEE32.scaledMagnitude (weightWord reference p row column) ≤ b.magnitude) &&
      quantized[p.matrix.coefficientOffset + row * p.matrix.inputWidth + column]! != 128) &&
    (if p.withBias then
      let bias := word reference (p.referenceBias + row)
      Wasm.IEEE32.isFinite bias &&
      decide (Wasm.IEEE32.scaledMagnitude bias ≤ b.biasMagnitude) &&
      bias == LeanExe.Packed.getUInt32LE! quantized (p.quantizedBias + row * 4)
    else true)

structure VectorBounds where
  magnitude : Nat
  sum : Nat
  deriving Inhabited

def profileVector (input : ByteArray) : VectorBounds := Id.run do
  let mut magnitude := 0
  let mut total := 0
  for i in [:input.size / 4] do
    let current := Wasm.IEEE32.scaledMagnitude (word input i)
    magnitude := max magnitude current
    total := total + current
  return ⟨magnitude, total⟩

def checkVector (input : ByteArray) (width : Nat) (b : VectorBounds) : Bool :=
  input.size == width * 4 &&
    decide (magnitudeSum (fun i => word input i) width ≤ b.sum) &&
    (List.range width).all (fun i => Wasm.IEEE32.isFinite (word input i) &&
      decide (Wasm.IEEE32.scaledMagnitude (word input i) ≤ b.magnitude))

def activationScaleMagnitude (input : ByteArray) : Nat :=
  (List.range (input.size / 256)).foldl (fun maximum group =>
    max maximum (Wasm.IEEE32.scaledMagnitude (Quantized.rowScale input (group * 64) 64))) 0

def checkActivations (input : ByteArray) (scaleMagnitude : Nat) : Bool :=
  let groups := input.size / 256
  let quantized := Quantized.quantizeRows input 64 groups
  input.size % 256 == 0 &&
    (List.range groups).all (fun group =>
      let scale := word quantized.scales group
      let values := input.extract (group * 256) ((group + 1) * 256)
      QuantizedExport.checkRow values quantized.values (group * 64) 64 scale &&
      decide (Wasm.IEEE32.scaledMagnitude scale ≤ scaleMagnitude) &&
      (List.range 64).all (fun i =>
        decide (Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.divBits (word values i) scale) ≤
          127 * 2 ^ 149 + 2 ^ 132)))

structure Parameters where
  referenceMul : Nat
  referenceAdd : Nat
  referenceBias : Nat
  quantizedScale : Nat
  quantizedOutput : Nat
  quantizedAdd : Nat
  quantizedBias : Nat
  deriving Inhabited

def sumMagnitude (count productBound addBound : Nat) : Nat :=
  count * (F32UniformRange.productMagnitude productBound + 2 ^ (addBound - 25))

def profileRanges (width inputMagnitude activationMagnitude : Nat) (w : WeightBounds) : Parameters :=
  let rm := max 173 ((inputMagnitude * w.magnitude).log2 + 1)
  let ra := (width * F32UniformRange.productMagnitude rm).log2 + 2
  let rb := (sumMagnitude width rm ra + w.biasMagnitude).log2 + 1
  let qs := max 173 ((activationMagnitude * w.scaleMagnitude).log2 + 1)
  let qo := max 173 (((1032256 * 2 ^ 149) * F32UniformRange.productMagnitude qs).log2 + 1)
  let qa := ((width / 64) * F32UniformRange.productMagnitude qo).log2 + 2
  let qb := (sumMagnitude (width / 64) qo qa + w.biasMagnitude).log2 + 1
  ⟨rm, ra, rb, qs, qo, qa, qb⟩

def checkRanges (width inputMagnitude activationMagnitude : Nat) (w : WeightBounds) (p : Parameters) : Bool :=
  F32UniformRange.dotFits width inputMagnitude w.magnitude p.referenceMul p.referenceAdd &&
    F32UniformRange.rescaleFits activationMagnitude w.scaleMagnitude p.quantizedScale p.quantizedOutput &&
    F32UniformRange.sumFits (width / 64) (F32UniformRange.productMagnitude p.quantizedOutput) p.quantizedAdd &&
    p.referenceBias ≤ 276 && p.quantizedBias ≤ 276 &&
    decide (sumMagnitude width p.referenceMul p.referenceAdd + w.biasMagnitude < 2 ^ p.referenceBias) &&
    decide (sumMagnitude (width / 64) p.quantizedOutput p.quantizedAdd + w.biasMagnitude < 2 ^ p.quantizedBias)

end Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
