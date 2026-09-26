import Project.ProofKit.QuantizedExportCheck
import LeanExe.Models.Gpt2.Quantized.Format
import LeanExe.Models.Gpt2.Inference

namespace Project.Gpt2QuantizedCached.Export
open Project.ProofKit LeanExe.Models

structure Projection where
  inputWidth : Nat
  outputWidth : Nat
  sourceOffset : Nat
  rowStride : Nat
  columnStride : Nat
  coefficientOffset : Nat
  scaleOffset : Nat
  deriving Inhabited

def projections : List Projection :=
  [{ inputWidth := 768, outputWidth := 50257, sourceOffset := 0,
      rowStride := 768, columnStride := 1, coefficientOffset := Gpt2.Quantized.tokenWeightOffset,
      scaleOffset := Gpt2.Quantized.tokenScaleOffset }] ++
    (List.range 12).flatMap fun layer =>
      let source := Gpt2.blocksOffset + layer * Gpt2.blockWords
      let target := Gpt2.Quantized.blocksOffset + layer * Gpt2.Quantized.blockBytes
      [{ inputWidth := 768, outputWidth := 2304, sourceOffset := source + Gpt2.qkvWeightOffset,
         rowStride := 1, columnStride := 2304, coefficientOffset := target + Gpt2.Quantized.qkvWeightOffset,
         scaleOffset := target + Gpt2.Quantized.qkvScaleOffset },
       { inputWidth := 768, outputWidth := 768, sourceOffset := source + Gpt2.attnWeightOffset,
         rowStride := 1, columnStride := 768, coefficientOffset := target + Gpt2.Quantized.attnWeightOffset,
         scaleOffset := target + Gpt2.Quantized.attnScaleOffset },
       { inputWidth := 768, outputWidth := 3072, sourceOffset := source + Gpt2.fcWeightOffset,
         rowStride := 1, columnStride := 3072, coefficientOffset := target + Gpt2.Quantized.fcWeightOffset,
         scaleOffset := target + Gpt2.Quantized.fcScaleOffset },
       { inputWidth := 3072, outputWidth := 768, sourceOffset := source + Gpt2.mlpWeightOffset,
         rowStride := 1, columnStride := 768, coefficientOffset := target + Gpt2.Quantized.mlpWeightOffset,
         scaleOffset := target + Gpt2.Quantized.mlpScaleOffset }]

structure Retained where
  sourceOffset : Nat
  targetOffset : Nat
  count : Nat
  deriving Inhabited

def retained : List Retained :=
  [{ sourceOffset := Gpt2.positionOffset, targetOffset := Gpt2.Quantized.positionOffset, count := 1024 * 768 },
   { sourceOffset := Gpt2.finalNormOffset, targetOffset := Gpt2.Quantized.finalNormOffset, count := 1536 }] ++
    (List.range 12).flatMap fun layer =>
      let source := Gpt2.blocksOffset + layer * Gpt2.blockWords
      let target := Gpt2.Quantized.blocksOffset + layer * Gpt2.Quantized.blockBytes
      [{ sourceOffset := source, targetOffset := target, count := 1536 },
       { sourceOffset := source + Gpt2.qkvBiasOffset, targetOffset := target + Gpt2.Quantized.qkvBiasOffset, count := 2304 },
       { sourceOffset := source + Gpt2.attnBiasOffset, targetOffset := target + Gpt2.Quantized.attnBiasOffset, count := 2304 },
       { sourceOffset := source + Gpt2.fcBiasOffset, targetOffset := target + Gpt2.Quantized.fcBiasOffset, count := 3072 },
       { sourceOffset := source + Gpt2.mlpBiasOffset, targetOffset := target + Gpt2.Quantized.mlpBiasOffset, count := 768 }]

def sourceRow (source : ByteArray) (projection : Projection) (row : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE projection.inputWidth fun i =>
    Gpt2.word source (projection.sourceOffset + row * projection.rowStride + i * projection.columnStride)

def checkProjection (source target : ByteArray) (projection : Projection) : Bool :=
  (List.range projection.outputWidth).all fun row =>
    QuantizedExport.checkRow (sourceRow source projection row) target
      (projection.coefficientOffset + row * projection.inputWidth) projection.inputWidth
      (LeanExe.Packed.getUInt32LE! target (projection.scaleOffset + row * 4))

def checkRetained (source target : ByteArray) (tensor : Retained) : Bool :=
  (List.range tensor.count).all fun i =>
    let original := Gpt2.word source (tensor.sourceOffset + i)
    Wasm.IEEE32.isFinite original &&
      original == LeanExe.Packed.getUInt32LE! target (tensor.targetOffset + i * 4)

def check (source target : ByteArray) : Bool :=
  source.size == Gpt2.parameterWords * 4 && Gpt2.Quantized.validHeader target &&
    projections.all (checkProjection source target) && retained.all (checkRetained source target)

end Project.Gpt2QuantizedCached.Export
