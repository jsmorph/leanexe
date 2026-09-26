import Project.ProofKit.QuantizedExportCheck

open Project.ProofKit LeanExe.Models.Gpt2

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | throw (IO.userError "usage: CheckActivations <groups.bin>")
  let bytes ← IO.FS.readBinFile path
  if bytes.size == 0 || bytes.size % 324 != 0 then
    throw (IO.userError "activation record extent mismatch")
  let mut maxScale : UInt32 := 0
  let mut maxQuotient : UInt32 := 0
  for group in [:bytes.size / 324] do
    let start := group * 324
    let input := bytes.extract start (start + 256)
    let scale := LeanExe.Packed.getUInt32LE! bytes (start + 256)
    if !QuantizedExport.checkRow input bytes (start + 260) 64 scale then
      throw (IO.userError s!"activation group {group} failed its scale, coefficient, or quotient check")
    maxScale := max maxScale scale
    for i in [:64] do
      let quotient := Wasm.IEEE32.div (word input i) scale &&& 0x7FFFFFFF
      maxQuotient := max maxQuotient quotient
    if (group + 1) % 10000 == 0 then
      IO.println s!"checked activation groups {group + 1}"
      (← IO.getStdout).flush
  IO.println s!"checked groups {bytes.size / 324} coefficients {bytes.size / 324 * 64} max_scale_bits {maxScale.toNat} max_abs_quotient_bits {maxQuotient.toNat}"
  return 0
