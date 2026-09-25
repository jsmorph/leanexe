import Project.Gpt2QuantizedCached.Numerical.ForwardUpper
import Lean.Data.Json

open LeanExe.Models.Gpt2 Project.ProofKit
open Project.Gpt2QuantizedCached.Numerical

def rows (path : System.FilePath) (columns : Nat) : IO (Array (Array Nat)) := do
  let mut result := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let fields ← (line.splitOn " ").toArray.mapM fun s =>
      match s.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"Invalid natural number in {path}")
    if fields.size != columns then throw (IO.userError s!"Wrong profile column count in {path}")
    result := result.push fields
  return result

def normParameters (r : Array Nat) : Project.Gpt2CachedStep.LayerNorm.RangeCertificate.Parameters :=
  ⟨r[1]!, r[2]!, r[3]!, r[4]!, r[5]!, r[6]!, r[7]!, r[8]!, r[9]!, r[10]!, r[11]!, r[12]!, r[13]!⟩

def normMagnitude (bytes : ByteArray) (index : Nat) : Nat × Nat := Id.run do
  let record := bytes.extract (index * 9216) ((index + 1) * 9216)
  let input := record.extract 0 3072
  let mean := LeanExe.Float32.divBits (Project.Gpt2CachedStep.LayerNorm.RangeCertificate.meanSum input) 0x44400000
  let mut center := 0
  let mut gain := 0
  for i in [:768] do
    center := max center (Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.subBits (word input i) mean))
    gain := max gain (Wasm.IEEE32.scaledMagnitude (word record (768 + i)))
  return (DyadicUpper.fp32Magnitude center, DyadicUpper.fp32Magnitude gain)

def normData (profiles : Array (Array Nat)) (bytes : ByteArray) (traceIndex index : Nat) : NormalizationUpper.PairData :=
  let q := traceIndex * 50 + index
  let r := q + 25
  let qm := normMagnitude bytes q
  let rm := normMagnitude bytes r
  ⟨normParameters profiles[q]!, normParameters profiles[r]!, qm.1, rm.1,
    2 * DyadicUpper.fp32Magnitude profiles[r]![1]!, max qm.2 rm.2⟩

def projectData (weights profiles : Array (Array Nat)) (traceIndex index : Nat) : OperationUpper.ProjectionData :=
  let p := profiles[traceIndex * 49 + index]!
  let w := weights[index]!
  ⟨⟨p[9]!, p[10]!, p[11]!, p[12]!, p[13]!, p[14]!, p[15]!⟩,
    DyadicUpper.fp32Magnitude p[4]!, DyadicUpper.fp32Magnitude w[1]!,
    DyadicUpper.mul (DyadicUpper.fp32Magnitude p[8]!) (DyadicUpper.fraction 32769 65536),
    DyadicUpper.mul (DyadicUpper.fp32Magnitude w[3]!) (DyadicUpper.fraction 98305 65536)⟩

def attentionParameters (r : Array Nat) : Project.Gpt2CachedStep.CachedAttention.RangeCertificate.Parameters :=
  ⟨r[5]!, r[6]!, r[7]!, ⟨r[8]!, r[9]!, r[10]!, {}⟩, r[11]!, r[12]!, r[13]!⟩

def main (args : List String) : IO UInt32 := do
  let [directory, coveragePath, outputPath] := args
    | throw (IO.userError "usage: EvaluateForward <capture-directory> <coverage.json> <bounds.txt>")
  let base : System.FilePath := directory
  let normalization ← rows (base / "normalization/ranges-ordered.txt") 15
  let normBytes ← IO.FS.readBinFile (base / "normalization/rows.bin")
  let weights ← rows (base / "projection-ranges/ranges.weights.txt") 5
  let projections ← rows (base / "projection-ranges/ranges.rows.txt") 16
  let attention ← rows (base / "nonlinear/attention-ranges.txt") 14
  let embeddings ← rows (base / "pointwise/ranges.embedding.txt") 6
  let residuals ← rows (base / "pointwise/ranges.residual.txt") 3
  let coverage ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile coveragePath))
  let sequences ← IO.ofExcept (coverage.getObjValAs? (Array Lean.Json) "sequences")
  let measurements ← IO.ofExcept (coverage.getObjValAs? (Array Lean.Json) "measurements")
  let n := measurements.size
  if n == 0 || weights.size != 49 || normalization.size != n * 50 || normBytes.size != n * 50 * 9216 ||
      projections.size != n * 49 || attention.size != n * 24 || embeddings.size != n || residuals.size != n * 24 then
    throw (IO.userError "Forward profile extent mismatch")
  let started ← IO.monoMsNow
  IO.FS.withFile outputPath .write fun output => do
    let mut index := 0
    for sequence in [:sequences.size] do
      let tokens ← IO.ofExcept (sequences[sequence]!.getObjValAs? (Array Nat) "tokens")
      if tokens.size == 0 || tokens.size > 128 then throw (IO.userError "Forward sequence extent mismatch")
      let mut cacheError := 0
      let mut keyMagnitude := Array.replicate 12 0
      for position in [:tokens.size] do
        if index >= n then throw (IO.userError "Forward profiles ended before the retained sequence")
        let measuredSequence ← IO.ofExcept (measurements[index]!.getObjValAs? Nat "sequence")
        let measuredPosition ← IO.ofExcept (measurements[index]!.getObjValAs? Nat "position")
        if measuredSequence != sequence || measuredPosition != position || embeddings[index]![1]! != tokens[position]! ||
            embeddings[index]![2]! != position then throw (IO.userError "Forward profile token order mismatch")
        let mut blocks := #[]
        for layer in [:12] do
          let matrix := index * 49 + layer * 4
          let row := projections[matrix]!
          if row[0]! != index || row[1]! != layer * 4 then throw (IO.userError "Projection profile order mismatch")
          keyMagnitude := keyMagnitude.set! layer (max keyMagnitude[layer]! (DyadicUpper.fp32Magnitude row[7]!))
          let q := attention[index * 24 + layer]!
          let r := attention[index * 24 + 12 + layer]!
          if q[1]! != sequence || q[2]! != position || q[3]! != 0 || q[4]! != layer ||
              r[1]! != sequence || r[2]! != position || r[3]! != 1 || r[4]! != layer then
            throw (IO.userError "Attention profile order mismatch")
          let a := residuals[index * 24 + layer * 2]!
          let b := residuals[index * 24 + layer * 2 + 1]!
          let d : ForwardUpper.BlockData := ⟨normData normalization normBytes index (layer * 2),
            projectData weights projections index (layer * 4), DyadicUpper.fp32Magnitude row[6]!, keyMagnitude[layer]!,
            attentionParameters q, attentionParameters r, projectData weights projections index (layer * 4 + 1), a[1]!, a[2]!,
            normData normalization normBytes index (layer * 2 + 1), projectData weights projections index (layer * 4 + 2),
            projectData weights projections index (layer * 4 + 3), b[1]!, b[2]!⟩
          blocks := blocks.push d
        let some first := blocks[0]? | throw (IO.userError "Empty forward block list")
        let emb := embeddings[index]!
        let vocabulary := projectData weights projections index 48
        let d : ForwardUpper.StepData := ⟨vocabulary.weightError, emb[3]!, emb[4]!, emb[5]!,
          fun i => (blocks[i]?).getD first, normData normalization normBytes index 24, vocabulary⟩
        let result := ForwardUpper.step d position cacheError
        cacheError := result.2
        output.putStrLn s!"{index} {sequence} {position} {result.1} {result.2}"
        index := index + 1
      output.flush
      IO.println s!"Evaluated forward sequence {sequence}, prefixes {index}, milliseconds {(← IO.monoMsNow) - started}"
      (← IO.getStdout).flush
    if index != n then throw (IO.userError "Unused forward profiles")
  IO.println s!"Forward evaluation passed: {n} prefixes, milliseconds {(← IO.monoMsNow) - started}"
  return 0
