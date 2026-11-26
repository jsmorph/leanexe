module

public import Examples.Lists.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/exampleLists.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Lists.File

file_theorems exampleLists compiled "../../build/verified/exampleLists.wasm" from compiled.bytes

end Examples.Lists.File
