import Library.Numerics.Reductions.Word.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libwordreductions.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Reductions.Word.File

file_theorems libwordreductions compiled "../../../../build/verified/libwordreductions.wasm"
  from compiled.bytes

end Library.Numerics.Reductions.Word.File
