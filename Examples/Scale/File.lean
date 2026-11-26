module

public import Examples.Scale.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/scale.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Scale.File

file_theorems scale compiled "../../build/verified/scale.wasm" from compiled.bytes

end Examples.Scale.File
