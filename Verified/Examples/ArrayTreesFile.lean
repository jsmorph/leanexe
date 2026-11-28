module

public import Verified.Examples.ArrayTrees
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/arraytrees.wasm`: the file holds
`encode ArrayTrees.compiled.module`, and it decodes to the module of `ArrayTrees.compiled.bytes`. -/

namespace Verified.Examples.ArrayTreesFile

file_theorems arraytrees ArrayTrees.compiled "../../build/verified/arraytrees.wasm"
  from ArrayTrees.compiled.bytes

end Verified.Examples.ArrayTreesFile
