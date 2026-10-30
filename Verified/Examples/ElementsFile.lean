import Verified.Examples.Elements
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/elements.wasm`: the file holds
`encode Elements.compiled.module`, and it decodes to the module of `Elements.compiled.bytes`. -/

namespace Verified.Examples.ElementsFile

file_theorems elements Elements.compiled "../../build/verified/elements.wasm"
  from Elements.compiled.bytes

end Verified.Examples.ElementsFile
