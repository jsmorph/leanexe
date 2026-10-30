import Examples.Increment.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/increment.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Increment.File

file_theorems increment compiled "../../build/verified/increment.wasm" from compiled.bytes

end Examples.Increment.File
