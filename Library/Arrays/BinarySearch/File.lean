import Library.Arrays.BinarySearch.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/binarySearch.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.BinarySearch.File

file_theorems binarySearch compiled "../../../build/verified/binarySearch.wasm" from compiled.bytes

end Library.Arrays.BinarySearch.File
