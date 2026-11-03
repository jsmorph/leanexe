import Library.Graphs.Dijkstra.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/dijkstra.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Graphs.Dijkstra.File

file_theorems dijkstra compiled "../../../build/verified/dijkstra.wasm"
  from compiled.bytes

end Library.Graphs.Dijkstra.File
