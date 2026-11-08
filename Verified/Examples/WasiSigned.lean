import Verified.Wasi

/-! A WASI command over `Int64`: `signedStep` reads up to 8 bytes, writes the low byte of
`x / 3 - 7` and returns it when the read gave bytes, and returns `-x` otherwise.  `main` applies it
to -40 and exits with 1 when the result is negative. -/

namespace Verified.Examples.WasiSigned

open LeanExe LeanExe.Wasi

def signedStep (x : Int64) : Action Int64 := do
  let input ← readSome 8
  if input.errno != 0 || input.bytes.size == 0 then
    pure (-x)
  else
    let y := x / 3 - 7
    let output ← writeStdoutSome (Bytes.build 1 fun _ => y.toUInt64 &&& 255)
    if output.errno != 0 then pure x else pure y

def main : Action UInt64 := do
  let y ← signedStep (-40)
  pure (if y < 0 then 1 else 0)

verified_compile_wasi callable := [signedStep, main]
verified_compile_wasi command (main := main) := [signedStep, main]

end Verified.Examples.WasiSigned
