import Library.Trees.Avl.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/avlTree.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Trees.Avl.File

file_theorems avlTree compiled "../../../build/verified/avlTree.wasm" from compiled.bytes

end Library.Trees.Avl.File
