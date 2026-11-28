module

public import Examples.TreeLookup.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/treeLookup.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.TreeLookup.File

file_theorems treeLookup compiled "../../build/verified/treeLookup.wasm" from compiled.bytes

end Examples.TreeLookup.File
