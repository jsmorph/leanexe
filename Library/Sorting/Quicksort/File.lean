import Library.Sorting.Quicksort.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/quicksort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.Quicksort.File

file_theorems quicksort compiled "../../../build/verified/quicksort.wasm" from compiled.bytes

end Library.Sorting.Quicksort.File
