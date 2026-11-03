import Library.Sorting.Shellsort.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/shellsort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.Shellsort.File

file_theorems shellsort compiled "../../../build/verified/shellsort.wasm" from compiled.bytes

end Library.Sorting.Shellsort.File
