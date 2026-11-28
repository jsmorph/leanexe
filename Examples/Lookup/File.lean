module

public import Examples.Lookup.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/lookup.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Lookup.File

file_theorems lookup compiled "../../build/verified/lookup.wasm" from compiled.bytes

end Examples.Lookup.File
