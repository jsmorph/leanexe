import Examples.Floor.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/floor.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Floor.File

file_theorems floor compiled "../../build/verified/floor.wasm" from compiled.bytes

end Examples.Floor.File
