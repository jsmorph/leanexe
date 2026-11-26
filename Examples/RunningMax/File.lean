module

public import Examples.RunningMax.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/runningMax.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.RunningMax.File

file_theorems runningMax compiled "../../build/verified/runningMax.wasm" from compiled.bytes

end Examples.RunningMax.File
