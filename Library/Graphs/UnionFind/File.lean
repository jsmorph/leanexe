import Library.Graphs.UnionFind.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/unionFind.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Graphs.UnionFind.File

file_theorems unionFind compiled "../../../build/verified/unionFind.wasm" from compiled.bytes

end Library.Graphs.UnionFind.File
