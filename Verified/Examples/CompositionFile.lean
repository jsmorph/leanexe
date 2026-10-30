import Verified.Examples.Composition
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/composition.wasm`: the file holds
`encode Composition.module`, and it decodes to `Composition.module`, which has no bytes theorem. -/

namespace Verified.Examples.CompositionFile

file_theorems composition Composition "../../build/verified/composition.wasm"

end Verified.Examples.CompositionFile
