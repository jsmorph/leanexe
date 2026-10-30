import Examples.SumCount.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sumCount.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.SumCount.File

file_theorems sumCount compiled "../../build/verified/sumCount.wasm" from compiled.bytes

end Examples.SumCount.File
