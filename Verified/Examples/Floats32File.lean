import Verified.Examples.Floats32
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/floats32.wasm`: the file holds
`encode Floats32.compiled.module`, and it decodes to the module of `Floats32.compiled.bytes`. -/

namespace Verified.Examples.Floats32File

file_theorems floats32 Floats32.compiled "../../build/verified/floats32.wasm"
  from Floats32.compiled.bytes

end Verified.Examples.Floats32File
