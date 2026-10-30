import Library.Numerics.Float64.Tanh.TanhBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tanh.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Tanh/TanhFile.lean`: the file holds
`encode Tanh.compiled.module`, so it decodes to the module of `TanhBytes.tanh_module_accuracy`,
which states the byte theorems of both `expm1` and `tanh`. -/

namespace Library.Numerics.Float64.Tanh.TanhFile

file_theorems tanh Tanh.compiled "../../../../build/verified/tanh.wasm"
  from TanhBytes.tanh_module_accuracy

end Library.Numerics.Float64.Tanh.TanhFile
