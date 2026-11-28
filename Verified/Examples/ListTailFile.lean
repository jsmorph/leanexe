module

public import Verified.Examples.ListTail
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/listtail.wasm`: the file holds
`encode ListTail.compiled.module`, and it decodes to the module of `ListTail.compiled.bytes`. -/

namespace Verified.Examples.ListTailFile

file_theorems listtail ListTail.compiled "../../build/verified/listtail.wasm"
  from ListTail.compiled.bytes

end Verified.Examples.ListTailFile
