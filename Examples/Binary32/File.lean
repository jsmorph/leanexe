import Examples.Binary32.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/binary32.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Binary32.File

file_theorems binary32 compiled "../../build/verified/binary32.wasm" from compiled.bytes

end Examples.Binary32.File
