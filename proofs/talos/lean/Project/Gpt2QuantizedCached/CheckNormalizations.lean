import Project.Gpt2CachedStep.LayerNorm.RangeProfile

open Project.Gpt2CachedStep.LayerNorm.RangeCertificate Project.ProofKit

def main (args : List String) : IO UInt32 := do
  let [path, outputPath] := args
    | throw (IO.userError "usage: CheckNormalizations <rows.bin> <ranges.txt>")
  let bytes ← IO.FS.readBinFile path
  if bytes.size == 0 || bytes.size % 9216 != 0 then
    throw (IO.userError "normalization record extent mismatch")
  IO.FS.withFile outputPath .write fun output => do
    for index in [:bytes.size / 9216] do
      let start := index * 9216
      let input := bytes.extract start (start + 3072)
      let weights := bytes.extract (start + 3072) (start + 9216)
      let p := profile weights input 0 768
      if !check weights input 0 768 p then
        throw (IO.userError s!"normalization record {index} failed an arithmetic range check")
      let mean := LeanExe.Float32.divBits (meanSum input) 0x44400000
      let total := varianceSum input mean
      let denominator := LeanExe.Float32.sqrtBits (LeanExe.Float32.addBits (LeanExe.Float32.divBits total 0x44400000) 0x3727C5AC)
      if !F32RangeCertificate.lowerAbsolute denominator 1 1000 then
        throw (IO.userError s!"normalization record {index} failed its denominator lower bound")
      output.putStrLn s!"{index} {p.inputMagnitude} {p.meanAdd} {p.meanDiv} {p.centerSub} {p.varianceMul} {p.varianceAdd} {p.varianceDiv} {p.epsilonAdd} {p.squareRoot} {p.reciprocal} {p.normalizedMul} {p.scaleMul} {p.biasAdd} {denominator.toNat}"
      if (index + 1) % 100 == 0 then
        output.flush
        IO.println s!"checked normalization records {index + 1}"
        (← IO.getStdout).flush
  return 0
