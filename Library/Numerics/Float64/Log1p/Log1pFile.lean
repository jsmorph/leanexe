import Library.Numerics.Float64.Log1p.Log1pBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/log1p.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Log1p/Log1pFile.lean`: the file holds
`encode Log1p.compiled.module`, so it decodes to the module of
`Log1pBytes.log1p_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Log1p.Log1pFile

file_theorems log1p Log1p.compiled "../../../../build/verified/log1p.wasm"
  from Log1pBytes.log1p_bytes_accuracy

end Library.Numerics.Float64.Log1p.Log1pFile
