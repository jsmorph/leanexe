import Demos.Gpt32.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/gpt32.wasm`: the file holds
`encode Verified.compiled.module`, and it decodes to the module of `Verified.compiled.bytes`. -/

namespace Demos.Gpt32.File

file_theorems gpt32 Verified.compiled "../../build/verified/gpt32.wasm" from Verified.compiled.bytes

end Demos.Gpt32.File
