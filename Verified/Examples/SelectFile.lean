module

public import Verified.Examples.Select
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/select.wasm`: the file holds
`encode Select.compiled.module`, and it decodes to the module of `Select.compiled.bytes`. -/

namespace Verified.Examples.SelectFile

file_theorems select Select.compiled "../../build/verified/select.wasm" from Select.compiled.bytes

end Verified.Examples.SelectFile
