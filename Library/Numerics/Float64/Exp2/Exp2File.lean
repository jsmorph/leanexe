import Library.Numerics.Float64.Exp2.Exp2Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/exp2.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Exp2/Exp2File.lean`: the file holds
`encode Exp2.compiled.module`, so it decodes to the module of `Exp2Bytes.exp2_module_accuracy`,
which states the byte theorems of both `exp2` and `exp10`. -/

namespace Library.Numerics.Float64.Exp2.Exp2File

file_theorems exp2 Exp2.compiled "../../../../build/verified/exp2.wasm"
  from Exp2Bytes.exp2_module_accuracy

end Library.Numerics.Float64.Exp2.Exp2File
