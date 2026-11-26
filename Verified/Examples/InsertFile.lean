module

public import Verified.Examples.Insert
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/insert.wasm`: the file holds
`encode Insert.compiled.module`, and it decodes to the module of `Insert.compiled.bytes`. -/

namespace Verified.Examples.InsertFile

file_theorems insert Insert.compiled "../../build/verified/insert.wasm" from Insert.compiled.bytes

end Verified.Examples.InsertFile
