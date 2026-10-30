import Library.Numerics.Float64.Log2.Log2Theorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log2.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Log2/Log2File.lean`: the file holds
`encode Log2.compiled.module`, so it decodes to the module of `Log2Theorem.log2_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log2.Log2File

file_theorems log2 Log2.compiled "../../../../build/verified/log2.wasm"
  from Log2Theorem.log2_bytes_accuracy

end Library.Numerics.Float64.Log2.Log2File
