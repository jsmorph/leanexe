import Verified.Examples.Updates
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/updates.wasm`: the file holds
`encode Updates.compiled.module`, and it decodes to the module of `Updates.compiled.bytes`. -/

namespace Verified.Examples.UpdatesFile

file_theorems updates Updates.compiled "../../build/verified/updates.wasm"
  from Updates.compiled.bytes

end Verified.Examples.UpdatesFile
