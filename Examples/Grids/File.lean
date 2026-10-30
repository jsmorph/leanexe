import Examples.Grids.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/exampleGrids.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Grids.File

file_theorems exampleGrids compiled "../../build/verified/exampleGrids.wasm" from compiled.bytes

end Examples.Grids.File
