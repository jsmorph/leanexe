module

public import Verified.Examples.TreeCopy
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/treecopy.wasm`: the file holds
`encode TreeCopy.module`, and it decodes to `TreeCopy.module`, which has no bytes theorem. -/

namespace Verified.Examples.TreeCopyFile

file_theorems treecopy TreeCopy "../../build/verified/treecopy.wasm"

end Verified.Examples.TreeCopyFile
