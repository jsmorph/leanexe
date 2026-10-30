import Verified.Examples.Grow
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/grow.wasm`: the file holds
`encode Grow.compiled.module`, and it decodes to the module of `Grow.compiled.bytes`. -/

namespace Verified.Examples.GrowFile

file_theorems grow Grow.compiled "../../build/verified/grow.wasm" from Grow.compiled.bytes

end Verified.Examples.GrowFile
