import Demos.Clob.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/clob.wasm`: the file holds
`encode Verified.compiled.module`, and it decodes to the module of `Verified.compiled.bytes`. -/

namespace Demos.Clob.File

file_theorems clob Verified.compiled "../../build/verified/clob.wasm" from Verified.compiled.bytes

end Demos.Clob.File
