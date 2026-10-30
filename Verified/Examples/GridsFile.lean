import Verified.Examples.Grids
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/grids.wasm`: the file holds
`encode Grids.compiled.module`, and it decodes to the module of `Grids.compiled.bytes`. -/

namespace Verified.Examples.GridsFile

file_theorems grids Grids.compiled "../../build/verified/grids.wasm" from Grids.compiled.bytes

end Verified.Examples.GridsFile
