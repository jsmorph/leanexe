module

public import Verified.Examples.Forms
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/forms.wasm`: the file holds
`encode Forms.compiled.module`, and it decodes to the module of `Forms.compiled.bytes`. -/

namespace Verified.Examples.FormsFile

file_theorems forms Forms.compiled "../../build/verified/forms.wasm" from Forms.compiled.bytes

end Verified.Examples.FormsFile
