import Library.Combinatorics.DancingLinks.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/dancingLinks.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Combinatorics.DancingLinks.File

file_theorems dancingLinks compiled "../../../build/verified/dancingLinks.wasm" from compiled.bytes

end Library.Combinatorics.DancingLinks.File
