import Project.Gpt2CachedStep.CachedAttention.RangeCheck
import Lean.Data.Json

open Project.Gpt2CachedStep.CachedAttention.RangeCertificate

def main (args : List String) : IO UInt32 := do
  let [path, coveragePath, outputPath] := args
    | throw (IO.userError "usage: CheckAttention <attention.bin> <coverage.json> <ranges.txt>")
  let bytes ← IO.FS.readBinFile path
  let coverage ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile coveragePath))
  let sequences ← IO.ofExcept (coverage.getObjValAs? (Array Lean.Json) "sequences")
  let started ← IO.monoMsNow
  let index ← IO.FS.withFile outputPath .write fun output => do
    let mut index := 0
    for sequence in [:sequences.size] do
      let tokens ← IO.ofExcept (sequences[sequence]!.getObjValAs? (Array Nat) "tokens")
      if tokens.size == 0 || tokens.size > 128 then
        throw (IO.userError "attention sequence length must be between 1 and 128")
      let mut caches := #[ByteArray.empty, ByteArray.empty]
      for position in [:tokens.size] do
        for model in [:2] do
          let cache := caches[model]!
          if cache.size != position * 73728 then
            throw (IO.userError "attention cache extent mismatch")
          let mut updates := ByteArray.empty
          for layer in [:12] do
            let start := index * 9216
            if start + 9216 > bytes.size then
              throw (IO.userError "attention input ended before the retained prefixes")
            let qkv := bytes.extract start (start + 9216)
            let p := profile cache qkv layer position
            if !check cache qkv layer position p then
              throw (IO.userError s!"attention range check failed at sequence {sequence}, position {position}, model {model}, layer {layer}")
            output.putStrLn s!"{index} {sequence} {position} {model} {layer} {p.scoreMul} {p.scoreAdd} {p.scoreScale} {p.softmax.subtraction} {p.softmax.summation} {p.softmax.division} {p.valueMul} {p.valueAdd} {p.valueMagnitude}"
            updates := updates ++ qkv.extract 3072 9216
            index := index + 1
          caches := caches.set! model (cache ++ updates)
        if (position + 1) % 16 == 0 || position + 1 == tokens.size then
          output.flush
          IO.println s!"checked attention sequence {sequence}, prefix {position + 1}, records {index}, milliseconds {(← IO.monoMsNow) - started}"
          (← IO.getStdout).flush
    if index * 9216 != bytes.size then
      throw (IO.userError "attention input has unused records")
    return index
  IO.println s!"Attention range check passed: {index} records, milliseconds {(← IO.monoMsNow) - started}"
  return 0
