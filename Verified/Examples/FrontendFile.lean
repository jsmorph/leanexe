import Verified.Examples.Frontend
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/frontend.wasm`: the file holds
`encode Frontend.compiled.module`, and it decodes to the module of `Frontend.compiled.bytes`. -/

namespace Verified.Examples.FrontendFile

file_theorems frontend Frontend.compiled "../../build/verified/frontend.wasm"
  from Frontend.compiled.bytes

end Verified.Examples.FrontendFile
