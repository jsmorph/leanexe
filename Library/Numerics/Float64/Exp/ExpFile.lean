import Library.Numerics.Float64.Exp.ExpTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/exp.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Exp/ExpFile.lean`: the file holds
`encode Exp.compiled.module`, so it decodes to the module of `ExpTheorem.exp_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Exp.ExpFile

file_theorems exp Exp.compiled "../../../../build/verified/exp.wasm"
  from ExpTheorem.exp_bytes_accuracy

end Library.Numerics.Float64.Exp.ExpFile
