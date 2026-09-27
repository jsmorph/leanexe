import Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCheck

open Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate

def main (args : List String) : IO UInt32 := do
  let [referencePath, quantizedPath, rowsPath, outputPrefix] := args
    | throw (IO.userError "usage: CheckProjections <fp32.bin> <quantized.bin> <rows.bin> <output-prefix>")
  let reference ← IO.FS.readBinFile referencePath
  let quantized ← IO.FS.readBinFile quantizedPath
  let rows ← IO.FS.readBinFile rowsPath
  if reference.size != LeanExe.Models.Gpt2.parameterWords * 4 ||
      !LeanExe.Models.Gpt2.Quantized.validHeader quantized then
    throw (IO.userError "projection checkpoint extent or header mismatch")
  let modelWords := layouts.foldl (fun total p => total + p.matrix.inputWidth + p.matrix.outputWidth) 0
  let modelBytes := modelWords * 4
  if rows.size == 0 || rows.size % (modelBytes * 2) != 0 then
    throw (IO.userError "projection capture extent mismatch")
  let started ← IO.monoMsNow
  let weights ← IO.FS.withFile (outputPrefix ++ ".weights.txt") .write fun output => do
    let mut weights := #[]
    for index in [:layouts.size] do
      let p := layouts[index]!
      let w := profileWeights reference quantized p
      if !checkWeights reference quantized p w then
        throw (IO.userError s!"projection {index} failed its weight bounds")
      weights := weights.push w
      output.putStrLn s!"{index} {w.magnitude} {w.rowSum} {w.scaleMagnitude} {w.biasMagnitude}"
      output.flush
      IO.println s!"checked projection weights {index + 1}, milliseconds {(← IO.monoMsNow) - started}"
      (← IO.getStdout).flush
    return weights
  let prefixes := rows.size / (modelBytes * 2)
  IO.FS.withFile (outputPrefix ++ ".rows.txt") .write fun output => do
    for traceIndex in [:prefixes] do
      let mut qCursor := traceIndex * modelBytes * 2
      let mut rCursor := qCursor + modelBytes
      for index in [:layouts.size] do
        let p := layouts[index]!
        let inputBytes := p.matrix.inputWidth * 4
        let outputBytes := p.matrix.outputWidth * 4
        let qi := rows.extract qCursor (qCursor + inputBytes)
        let qo := rows.extract (qCursor + inputBytes) (qCursor + inputBytes + outputBytes)
        let ri := rows.extract rCursor (rCursor + inputBytes)
        let ro := rows.extract (rCursor + inputBytes) (rCursor + inputBytes + outputBytes)
        qCursor := qCursor + inputBytes + outputBytes
        rCursor := rCursor + inputBytes + outputBytes
        let qInput := profileVector qi
        let rInput := profileVector ri
        let qOutput := profileVector qo
        let rOutput := profileVector ro
        if !checkVector qi p.matrix.inputWidth qInput || !checkVector ri p.matrix.inputWidth rInput ||
            !checkVector qo p.matrix.outputWidth qOutput || !checkVector ro p.matrix.outputWidth rOutput then
          throw (IO.userError s!"projection {index}, prefix {traceIndex}, failed vector bounds")
        let activationMagnitude := activationScaleMagnitude qi
        if !checkActivations qi activationMagnitude then
          throw (IO.userError s!"projection {index}, prefix {traceIndex}, failed activation reconstruction conditions")
        let ranges := profileRanges p.matrix.inputWidth rInput.magnitude activationMagnitude weights[index]!
        if !checkRanges p.matrix.inputWidth rInput.magnitude activationMagnitude weights[index]! ranges then
          throw (IO.userError s!"projection {index}, prefix {traceIndex}, failed arithmetic ranges")
        output.putStrLn s!"{traceIndex} {index} {qInput.magnitude} {qInput.sum} {rInput.magnitude} {rInput.sum} {qOutput.magnitude} {rOutput.magnitude} {activationMagnitude} {ranges.referenceMul} {ranges.referenceAdd} {ranges.referenceBias} {ranges.quantizedScale} {ranges.quantizedOutput} {ranges.quantizedAdd} {ranges.quantizedBias}"
      if (traceIndex + 1) % 16 == 0 || traceIndex + 1 == prefixes then
        output.flush
        IO.println s!"checked projection prefixes {traceIndex + 1}, milliseconds {(← IO.monoMsNow) - started}"
        (← IO.getStdout).flush
  IO.println s!"Projection range check passed: {layouts.size} matrices, {prefixes} prefixes, milliseconds {(← IO.monoMsNow) - started}"
  return 0
