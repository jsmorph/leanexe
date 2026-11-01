import Examples.Trees.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/exampleTrees.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Trees.File

file_theorems exampleTrees compiled "../../build/verified/exampleTrees.wasm" from compiled.bytes

end Examples.Trees.File
