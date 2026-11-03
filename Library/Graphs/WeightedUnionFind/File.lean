import Library.Graphs.WeightedUnionFind.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/weightedUnionFind.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Graphs.WeightedUnionFind.File

file_theorems weightedUnionFind compiled "../../../build/verified/weightedUnionFind.wasm"
  from compiled.bytes

end Library.Graphs.WeightedUnionFind.File
