import Library.Numerics.Bounds.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libbounds.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Bounds.File

file_theorems libbounds compiled "../../../build/verified/libbounds.wasm" from compiled.bytes

end Library.Numerics.Bounds.File
