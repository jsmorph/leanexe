import Project.Gpt2QuantizedCached.Numerical.PointwiseRangeCheck

open LeanExe.Models.Gpt2 Project.Gpt2QuantizedCached
open Numerical.PointwiseRangeCertificate

def main (args : List String) : IO UInt32 := do
  let [referencePath, quantizedPath, embeddingPath, residualPath, outputPrefix] := args
    | throw (IO.userError "usage: CheckPointwise <fp32.bin> <quantized.bin> <embedding.bin> <residual.bin> <output-prefix>")
  let rw ← IO.FS.readBinFile referencePath
  let qw ← IO.FS.readBinFile quantizedPath
  let embeddings ← IO.FS.readBinFile embeddingPath
  let residuals ← IO.FS.readBinFile residualPath
  if rw.size != parameterWords * 4 || !Quantized.validHeader qw || embeddings.size == 0 ||
      embeddings.size % 6152 != 0 || residuals.size != embeddings.size / 6152 * 24 * 18432 then
    throw (IO.userError "pointwise input extent or model header mismatch")
  let started ← IO.monoMsNow
  IO.FS.withFile (outputPrefix ++ ".embedding.txt") .write fun output => do
    for index in [:embeddings.size / 6152] do
      let record := embeddings.extract (index * 6152) ((index + 1) * 6152)
      let token := word record 0
      let position := (word record 1).toNat
      if token.toNat ≥ 50257 || position ≥ 128 then
        throw (IO.userError s!"embedding token or position out of range at {index}")
      let p := profileEmbedding qw rw token position
      if !checkEmbedding qw rw token position p then
        throw (IO.userError s!"embedding range check failed at {index}")
      for i in [:768] do
        let q := LeanExe.Float32.addBits (Embedding.Error.reconstructed qw token i) (Embedding.Error.positionWord qw position i)
        let r := LeanExe.Float32.addBits (word rw (token.toNat * 768 + i)) (word rw (positionOffset + position * 768 + i))
        if q != word record (2 + i) || r != word record (770 + i) then
          throw (IO.userError s!"embedding output mismatch at {index}, coordinate {i}")
      output.putStrLn s!"{index} {token.toNat} {position} {p.multiplication} {p.quantizedAdd} {p.referenceAdd}"
  IO.println s!"checked embeddings {embeddings.size / 6152}, milliseconds {(← IO.monoMsNow) - started}"
  (← IO.getStdout).flush
  IO.FS.withFile (outputPrefix ++ ".residual.txt") .write fun output => do
    for index in [:residuals.size / 18432] do
      let mut bounds := #[]
      for model in [:2] do
        let start := index * 18432 + model * 9216
        let left := residuals.extract start (start + 3072)
        let right := residuals.extract (start + 3072) (start + 6144)
        let result := residuals.extract (start + 6144) (start + 9216)
        let bound := profileAdd left right
        if !checkAdd left right bound then
          throw (IO.userError s!"residual range check failed at {index}, model {model}")
        for i in [:768] do
          if LeanExe.Float32.addBits (word left i) (word right i) != word result i then
            throw (IO.userError s!"residual output mismatch at {index}, model {model}, coordinate {i}")
        bounds := bounds.push bound
      output.putStrLn s!"{index} {bounds[0]!} {bounds[1]!}"
      if (index + 1) % 768 == 0 then
        output.flush
        IO.println s!"checked residuals {index + 1}, milliseconds {(← IO.monoMsNow) - started}"
        (← IO.getStdout).flush
  IO.println s!"Pointwise range check passed: {embeddings.size / 6152} embeddings, {residuals.size / 18432} paired residuals, milliseconds {(← IO.monoMsNow) - started}"
  return 0
