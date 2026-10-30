import Library.Numerics.LinearAlgebra.Float64.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/liblinalg64.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.LinearAlgebra.Float64.File

file_theorems liblinalg64 compiled "../../../../build/verified/liblinalg64.wasm" from compiled.bytes

end Library.Numerics.LinearAlgebra.Float64.File
