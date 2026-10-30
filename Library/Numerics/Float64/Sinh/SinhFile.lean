import Library.Numerics.Float64.Sinh.SinhBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sinh.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Sinh/SinhFile.lean`: the file holds
`encode Sinh.compiled.module`, so it decodes to the module of `SinhBytes.sinh_module_accuracy`,
which states the byte theorems of both `sinh` and `cosh`. -/

namespace Library.Numerics.Float64.Sinh.SinhFile

file_theorems sinh Sinh.compiled "../../../../build/verified/sinh.wasm"
  from SinhBytes.sinh_module_accuracy

end Library.Numerics.Float64.Sinh.SinhFile
