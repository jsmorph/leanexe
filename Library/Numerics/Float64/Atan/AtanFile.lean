import Library.Numerics.Float64.Atan.AtanBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/atan.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Atan/AtanFile.lean`: the file holds
`encode Atan.compiled.module`, so it decodes to the module of `AtanBytes.atan_module_accuracy`,
which states the byte theorems of both `atan` and `atan2`. -/

namespace Library.Numerics.Float64.Atan.AtanFile

file_theorems atan Atan.compiled "../../../../build/verified/atan.wasm"
  from AtanBytes.atan_module_accuracy

end Library.Numerics.Float64.Atan.AtanFile
