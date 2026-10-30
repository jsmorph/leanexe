import Library.Numerics.Limiters.Minmod.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libminmod.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Limiters.Minmod.File

file_theorems libminmod compiled "../../../../build/verified/libminmod.wasm" from compiled.bytes

end Library.Numerics.Limiters.Minmod.File
