import Library.Numerics.LinearAlgebra.Binary32.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/liblinalg32.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.LinearAlgebra.Binary32.File

file_theorems liblinalg32 compiled "../../../../build/verified/liblinalg32.wasm" from compiled.bytes

end Library.Numerics.LinearAlgebra.Binary32.File
