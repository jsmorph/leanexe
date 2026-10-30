import Library.Numerics.Float64.Pow.PowBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/pow.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Pow/PowFile.lean`: the file holds
`encode Pow.compiled.module`, so it decodes to the module of `PowBytes.pow_bytes_accuracy`.
The kernel takes its recursion limit from `maxRecDepth`, and its check of the 11,156-byte literal
exceeds the default limit, so both theorems raise it. -/

namespace Library.Numerics.Float64.Pow.PowFile

file_theorems pow Pow.compiled "../../../../build/verified/pow.wasm"
  from PowBytes.pow_bytes_accuracy

end Library.Numerics.Float64.Pow.PowFile
