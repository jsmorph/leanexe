import Verified.Examples.Calls
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/calls.wasm`: the file holds
`encode Calls.compiled.module`, and it decodes to the module of `Calls.compiled.bytes`. -/

namespace Verified.Examples.CallsFile

file_theorems calls Calls.compiled "../../build/verified/calls.wasm" from Calls.compiled.bytes

end Verified.Examples.CallsFile
