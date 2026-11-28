module

public import Examples.Below100.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/below100.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Below100.File

file_theorems below100 compiled "../../build/verified/below100.wasm" from compiled.bytes

end Examples.Below100.File
