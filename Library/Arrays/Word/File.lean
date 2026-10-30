import Library.Arrays.Word.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libwordarray.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.Word.File

file_theorems libwordarray compiled "../../../build/verified/libwordarray.wasm" from compiled.bytes

end Library.Arrays.Word.File
