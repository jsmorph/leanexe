import Examples.SumArray.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sumArray.wasm`: the file holds
`encode compiledSum.module`, and it decodes to the module of `compiledSum.bytes`. -/

namespace Examples.SumArray.FileSum

file_theorems sumArray compiledSum "../../build/verified/sumArray.wasm" from compiledSum.bytes

end Examples.SumArray.FileSum
