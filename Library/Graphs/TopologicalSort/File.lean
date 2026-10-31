import Library.Graphs.TopologicalSort.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/topoSort.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Graphs.TopologicalSort.File

file_theorems topoSort compiled "../../../build/verified/topoSort.wasm" from compiled.bytes

end Library.Graphs.TopologicalSort.File
