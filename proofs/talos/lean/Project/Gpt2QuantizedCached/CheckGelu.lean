import Project.Gpt2CachedStep.GeluRangeCheck
import LeanExe.Models.Gpt2.Kernel

open Project.Gpt2CachedStep.GeluRangeCertificate

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: CheckGelu <words.bin>")
  let bytes ← IO.FS.readBinFile path
  if bytes.size == 0 || bytes.size % 4 != 0 then
    throw (IO.userError "GELU input extent mismatch")
  let started ← IO.monoMsNow
  for i in [:bytes.size / 4] do
    let input := LeanExe.Models.Gpt2.word bytes i
    if !check input {} then
      throw (IO.userError s!"GELU input {i}, bits {input.toNat}, failed an arithmetic range check")
    if (i + 1) % 10000 == 0 then
      IO.println s!"checked GELU inputs {i + 1}, milliseconds {(← IO.monoMsNow) - started}"
      (← IO.getStdout).flush
  IO.println s!"GELU range check passed: {bytes.size / 4} inputs, milliseconds {(← IO.monoMsNow) - started}"
  return 0
