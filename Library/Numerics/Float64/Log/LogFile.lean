import Library.Numerics.Float64.Log.LogTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Log/LogFile.lean`: the file holds
`encode Log.compiled.module`, so it decodes to the module of `LogTheorem.log_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log.LogFile

file_theorems log Log.compiled "../../../../build/verified/log.wasm"
  from LogTheorem.log_bytes_accuracy

end Library.Numerics.Float64.Log.LogFile
