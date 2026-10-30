import Library.Trees.WordTree.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libtrees.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Trees.WordTree.File

file_theorems libtrees compiled "../../../build/verified/libtrees.wasm" from compiled.bytes

end Library.Trees.WordTree.File
