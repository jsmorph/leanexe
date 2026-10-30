import Examples.Calc.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/calculator.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Calc.File

file_theorems calculator compiled "../../build/verified/calculator.wasm" from compiled.bytes

end Examples.Calc.File
