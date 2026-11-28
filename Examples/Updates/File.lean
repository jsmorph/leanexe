module

public import Examples.Updates.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/exampleUpdates.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Updates.File

file_theorems exampleUpdates compiled "../../build/verified/exampleUpdates.wasm" from compiled.bytes

end Examples.Updates.File
