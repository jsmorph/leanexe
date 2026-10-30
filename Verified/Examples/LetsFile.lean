import Verified.Examples.Lets
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/lets.wasm`: the file holds
`encode Lets.compiled.module`, and it decodes to the module of `Lets.compiled.bytes`. -/

namespace Verified.Examples.LetsFile

file_theorems lets Lets.compiled "../../build/verified/lets.wasm" from Lets.compiled.bytes

end Verified.Examples.LetsFile
