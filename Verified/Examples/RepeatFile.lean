import Verified.Examples.Repeat
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/repeat.wasm`: the file holds
`encode Repeat.compiled.module`, and it decodes to the module of `Repeat.compiled.bytes`. -/

namespace Verified.Examples.RepeatFile

file_theorems «repeat» Repeat.compiled "../../build/verified/repeat.wasm" from Repeat.compiled.bytes

end Verified.Examples.RepeatFile
