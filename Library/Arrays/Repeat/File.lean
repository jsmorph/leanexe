import Library.Arrays.Repeat.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/librepeat.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.Repeat.File

file_theorems librepeat compiled "../../../build/verified/librepeat.wasm" from compiled.bytes

end Library.Arrays.Repeat.File
