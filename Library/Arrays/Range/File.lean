import Library.Arrays.Range.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/librange.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.Range.File

file_theorems librange compiled "../../../build/verified/librange.wasm" from compiled.bytes

end Library.Arrays.Range.File
