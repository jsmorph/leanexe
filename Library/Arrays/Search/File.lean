import Library.Arrays.Search.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libsearch.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.Search.File

file_theorems libsearch compiled "../../../build/verified/libsearch.wasm" from compiled.bytes

end Library.Arrays.Search.File
