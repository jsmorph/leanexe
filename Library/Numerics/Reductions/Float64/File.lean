import Library.Numerics.Reductions.Float64.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libfloatreductions.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Reductions.Float64.File

file_theorems libfloatreductions compiled "../../../../build/verified/libfloatreductions.wasm"
  from compiled.bytes

end Library.Numerics.Reductions.Float64.File
