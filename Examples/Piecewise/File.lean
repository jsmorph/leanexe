import Examples.Piecewise.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/piecewise.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Piecewise.File

file_theorems piecewise compiled "../../build/verified/piecewise.wasm" from compiled.bytes

end Examples.Piecewise.File
