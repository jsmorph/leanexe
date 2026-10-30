import Verified.Examples.RecursiveTypes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/recursivetypes.wasm`: the file
holds `encode RecursiveTypes.compiled.module`, and it decodes to the module of
`RecursiveTypes.compiled.bytes`. -/

namespace Verified.Examples.RecursiveTypesFile

file_theorems recursivetypes RecursiveTypes.compiled "../../build/verified/recursivetypes.wasm"
  from RecursiveTypes.compiled.bytes

end Verified.Examples.RecursiveTypesFile
