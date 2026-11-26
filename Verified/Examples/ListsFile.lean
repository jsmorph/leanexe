module

public import Verified.Examples.Lists
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/lists.wasm`: the file holds
`encode Lists.compiled.module`, and it decodes to the module of `Lists.compiled.bytes`. -/

namespace Verified.Examples.ListsFile

file_theorems lists Lists.compiled "../../build/verified/lists.wasm" from Lists.compiled.bytes

end Verified.Examples.ListsFile
