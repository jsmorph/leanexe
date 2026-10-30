import Examples.ScaledHypot.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/scaledHypot.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.ScaledHypot.File

file_theorems scaledHypot compiled "../../build/verified/scaledHypot.wasm" from compiled.bytes

end Examples.ScaledHypot.File
