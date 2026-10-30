import Demos.Euler.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/euler.wasm`: the file holds
`encode Verified.compiled.module`, and it decodes to the module of `Verified.compiled.bytes`. -/

namespace Demos.Euler.File

file_theorems euler Verified.compiled "../../build/verified/euler.wasm" from Verified.compiled.bytes

end Demos.Euler.File
