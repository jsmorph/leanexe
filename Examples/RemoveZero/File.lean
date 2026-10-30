import Examples.RemoveZero.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/removeZero.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.RemoveZero.File

file_theorems removeZero compiled "../../build/verified/removeZero.wasm" from compiled.bytes

end Examples.RemoveZero.File
