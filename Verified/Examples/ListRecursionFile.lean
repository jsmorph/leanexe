import Verified.Examples.ListRecursion
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/listrecursion.wasm`: the file holds
`encode ListRecursion.compiled.module`, and it decodes to the module of
`ListRecursion.compiled.bytes`. -/

namespace Verified.Examples.ListRecursionFile

file_theorems listrecursion ListRecursion.compiled "../../build/verified/listrecursion.wasm"
  from ListRecursion.compiled.bytes

end Verified.Examples.ListRecursionFile
