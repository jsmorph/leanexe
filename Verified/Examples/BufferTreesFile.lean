module

public import Verified.Examples.BufferTrees
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/buffertrees.wasm`: the file holds
`encode BufferTrees.compiled.module`, and it decodes to the module of `BufferTrees.compiled.bytes`.
-/

namespace Verified.Examples.BufferTreesFile

file_theorems buffertrees BufferTrees.compiled "../../build/verified/buffertrees.wasm"
  from BufferTrees.compiled.bytes

end Verified.Examples.BufferTreesFile
