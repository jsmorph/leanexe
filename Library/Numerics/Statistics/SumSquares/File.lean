import Library.Numerics.Statistics.SumSquares.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sumSquares.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Statistics.SumSquares.File

file_theorems sumSquares compiled "../../../../build/verified/sumSquares.wasm" from compiled.bytes

end Library.Numerics.Statistics.SumSquares.File
