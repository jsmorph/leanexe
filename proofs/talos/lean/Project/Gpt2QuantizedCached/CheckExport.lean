import Project.Gpt2QuantizedCached.Export

open Project.Gpt2QuantizedCached

def main (args : List String) : IO UInt32 := do
  let [sourcePath, targetPath] := args
    | throw (IO.userError "usage: CheckExport <fp32-weights.bin> <quantized-weights.bin>")
  let source ← IO.FS.readBinFile sourcePath
  let target ← IO.FS.readBinFile targetPath
  if source.size != LeanExe.Models.Gpt2.parameterWords * 4 ||
      !LeanExe.Models.Gpt2.Quantized.validHeader target then
    throw (IO.userError "checkpoint header or extent mismatch")
  let projections := Export.projections.toArray
  let mut coefficients := 0
  let mut scales := 0
  for i in [:projections.size] do
    let projection := projections[i]!
    if !Export.checkProjection source target projection then
      throw (IO.userError s!"quantized projection {i} differs from the specified export")
    coefficients := coefficients + projection.inputWidth * projection.outputWidth
    scales := scales + projection.outputWidth
    IO.println s!"projection {i} rows {projection.outputWidth} width {projection.inputWidth} checked"
  let tensors := Export.retained.toArray
  let mut retained := 0
  for i in [:tensors.size] do
    let tensor := tensors[i]!
    if !Export.checkRetained source target tensor then
      throw (IO.userError s!"retained FP32 tensor {i} differs from the checkpoint")
    retained := retained + tensor.count
  IO.println s!"checked coefficients {coefficients} scales {scales} retained {retained}"
  return 0
