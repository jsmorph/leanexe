module

public import Verified.Examples.Tail
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/tail.wasm`: the file holds
`encode Tail.compiled.module`, and it decodes to the module of `Tail.compiled.bytes`. -/

namespace Verified.Examples.TailFile

file_theorems tail Tail.compiled "../../build/verified/tail.wasm" from Tail.compiled.bytes

end Verified.Examples.TailFile
