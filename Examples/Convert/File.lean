import Examples.Convert.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/convert.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Convert.File

file_theorems convert compiled "../../build/verified/convert.wasm" from compiled.bytes

end Examples.Convert.File
