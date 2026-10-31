import Library.Sorting.MergeSort.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/mergeSort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.MergeSort.File

file_theorems mergeSort compiled "../../../build/verified/mergeSort.wasm" from compiled.bytes

end Library.Sorting.MergeSort.File
