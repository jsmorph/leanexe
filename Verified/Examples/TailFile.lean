import Verified.Examples.Tail
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tail.wasm`: the file holds
`encode Tail.compiled.module`, and it decodes to the module of `Tail.compiled.bytes`. -/

namespace Verified.Examples.TailFile

file_theorems tail Tail.compiled "../../build/verified/tail.wasm" from Tail.compiled.bytes

end Verified.Examples.TailFile
