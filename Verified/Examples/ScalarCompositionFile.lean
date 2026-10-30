import Verified.Examples.ScalarComposition
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/scalarcomposition.wasm`: the file
holds `encode ScalarComposition.compiled.module`, and it decodes to the module of
`ScalarComposition.compiled.bytes`. -/

namespace Verified.Examples.ScalarCompositionFile

file_theorems scalarcomposition ScalarComposition.compiled
  "../../build/verified/scalarcomposition.wasm"
  from ScalarComposition.compiled.bytes

end Verified.Examples.ScalarCompositionFile
