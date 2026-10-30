import Library.Numerics.Float64.Tan.TanTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tan.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Tan/TanFile.lean`: the file holds
`encode Tan.compiled.module`, so it decodes to the module of `TanTheorem.tan_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Tan.TanFile

file_theorems tan Tan.compiled "../../../../build/verified/tan.wasm"
  from TanTheorem.tan_bytes_accuracy

end Library.Numerics.Float64.Tan.TanFile
