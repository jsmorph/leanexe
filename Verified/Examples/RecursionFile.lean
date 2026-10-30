import Verified.Examples.Recursion
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/recursion.wasm`: the file holds
`encode Recursion.compiled.module`, and it decodes to the module of `Recursion.compiled.bytes`. -/

namespace Verified.Examples.RecursionFile

file_theorems recursion Recursion.compiled "../../build/verified/recursion.wasm"
  from Recursion.compiled.bytes

end Verified.Examples.RecursionFile
