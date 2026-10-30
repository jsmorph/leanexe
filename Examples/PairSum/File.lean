import Examples.PairSum.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/pairSum.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.PairSum.File

file_theorems pairSum compiled "../../build/verified/pairSum.wasm" from compiled.bytes

end Examples.PairSum.File
