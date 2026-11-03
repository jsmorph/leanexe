import Library.Sorting.RadixSort.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/radixSort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.RadixSort.File

file_theorems radixSort compiled "../../../build/verified/radixSort.wasm" from compiled.bytes

end Library.Sorting.RadixSort.File
