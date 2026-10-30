import Verified.Examples.Forms
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/forms.wasm`: the file holds
`encode Forms.compiled.module`, and it decodes to the module of `Forms.compiled.bytes`. -/

namespace Verified.Examples.FormsFile

file_theorems forms Forms.compiled "../../build/verified/forms.wasm" from Forms.compiled.bytes

end Verified.Examples.FormsFile
