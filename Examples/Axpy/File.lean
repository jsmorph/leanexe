import Examples.Axpy.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/axpy.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Axpy.File

file_theorems axpy compiled "../../build/verified/axpy.wasm" from compiled.bytes

end Examples.Axpy.File
