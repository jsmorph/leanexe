import Library.Sorting.Heapsort.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/heapsort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.Heapsort.File

file_theorems heapsort compiled "../../../build/verified/heapsort.wasm" from compiled.bytes

end Library.Sorting.Heapsort.File
