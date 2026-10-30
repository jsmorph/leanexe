import Verified.Examples.ListLoops
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/listloops.wasm`: the file holds
`encode ListLoops.compiled.module`, and it decodes to the module of `ListLoops.compiled.bytes`. -/

namespace Verified.Examples.ListLoopsFile

file_theorems listloops ListLoops.compiled "../../build/verified/listloops.wasm"
  from ListLoops.compiled.bytes

end Verified.Examples.ListLoopsFile
