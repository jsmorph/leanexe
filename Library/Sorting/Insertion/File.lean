import Library.Sorting.Insertion.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libsort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.Insertion.File

file_theorems libsort compiled "../../../build/verified/libsort.wasm" from compiled.bytes

end Library.Sorting.Insertion.File
