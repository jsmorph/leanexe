import Demos.Gpt.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/gpt.wasm`: the file holds
`encode Verified.compiled.module`, and it decodes to the module of `Verified.compiled.bytes`. -/

namespace Demos.Gpt.VerifiedFile

file_theorems gpt Verified.compiled "../../build/verified/gpt.wasm" from Verified.compiled.bytes

end Demos.Gpt.VerifiedFile
