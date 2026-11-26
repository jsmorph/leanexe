module

public import Library.Trees.Search.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/treeSearch.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Trees.Search.File

file_theorems treeSearch compiled "../../../build/verified/treeSearch.wasm" from compiled.bytes

end Library.Trees.Search.File
