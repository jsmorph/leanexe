import Library.Trees.AvlDelete.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/avlDelete.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Trees.AvlDelete.File

file_theorems avlDelete compiled "../../../build/verified/avlDelete.wasm" from compiled.bytes

end Library.Trees.AvlDelete.File
