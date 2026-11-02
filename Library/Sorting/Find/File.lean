import Library.Sorting.Find.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/find.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.Find.File

file_theorems find compiled "../../../build/verified/find.wasm" from compiled.bytes

end Library.Sorting.Find.File
