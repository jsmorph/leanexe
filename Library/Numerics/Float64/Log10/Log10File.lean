import Library.Numerics.Float64.Log10.Log10Theorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log10.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Log10/Log10File.lean`: the file holds
`encode Log10.compiled.module`, so it decodes to the module of `Log10Theorem.log10_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log10.Log10File

file_theorems log10 Log10.compiled "../../../../build/verified/log10.wasm"
  from Log10Theorem.log10_bytes_accuracy

end Library.Numerics.Float64.Log10.Log10File
