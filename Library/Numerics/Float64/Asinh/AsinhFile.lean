import Library.Numerics.Float64.Asinh.AsinhBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/asinh.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Asinh/AsinhFile.lean`: the file holds
`encode Asinh.compiled.module`, so it decodes to the module of
`AsinhBytes.asinh_module_accuracy`, which states the byte theorems of `atanh`, `asinh`, and
`acosh`. -/

namespace Library.Numerics.Float64.Asinh.AsinhFile

file_theorems asinh Asinh.compiled "../../../../build/verified/asinh.wasm"
  from AsinhBytes.asinh_module_accuracy

end Library.Numerics.Float64.Asinh.AsinhFile
