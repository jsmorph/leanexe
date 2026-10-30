import Library.Arrays.Filter.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libfilter.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.Filter.File

file_theorems libfilter compiled "../../../build/verified/libfilter.wasm" from compiled.bytes

end Library.Arrays.Filter.File
