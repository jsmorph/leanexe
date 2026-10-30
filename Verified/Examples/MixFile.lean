import Verified.Examples.Mix
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/mix.wasm`: the file holds
`encode Mix.compiled.module`, and it decodes to the module of `Mix.compiled.bytes`. -/

namespace Verified.Examples.MixFile

file_theorems mix Mix.compiled "../../build/verified/mix.wasm" from Mix.compiled.bytes

end Verified.Examples.MixFile
