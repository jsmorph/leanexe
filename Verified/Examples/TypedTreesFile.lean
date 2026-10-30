import Verified.Examples.TypedTrees
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/typedtrees.wasm`: the file holds
`encode TypedTrees.compiled.module`, and it decodes to the module of `TypedTrees.compiled.bytes`. -/

namespace Verified.Examples.TypedTreesFile

file_theorems typedtrees TypedTrees.compiled "../../build/verified/typedtrees.wasm"
  from TypedTrees.compiled.bytes

end Verified.Examples.TypedTreesFile
