import Examples.Bools.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/bools.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Bools.File

file_theorems bools compiled "../../build/verified/bools.wasm" from compiled.bytes

end Examples.Bools.File
