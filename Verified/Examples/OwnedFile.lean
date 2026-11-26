module

public import Verified.Examples.Owned
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/owned.wasm`: the file holds
`encode Owned.compiled.module`, and it decodes to the module of `Owned.compiled.bytes`. -/

namespace Verified.Examples.OwnedFile

file_theorems owned Owned.compiled "../../build/verified/owned.wasm" from Owned.compiled.bytes

end Verified.Examples.OwnedFile
