import Verified.Examples.Modes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/modes.wasm`: the file holds
`encode Modes.compiled.module`, and it decodes to the module of `Modes.compiled.bytes`. -/

namespace Verified.Examples.ModesFile

file_theorems modes Modes.compiled "../../build/verified/modes.wasm" from Modes.compiled.bytes

end Verified.Examples.ModesFile
