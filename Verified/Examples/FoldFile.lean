import Verified.Examples.Fold
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/fold.wasm`: the file holds
`encode Fold.compiled.module`, and it decodes to the module of `Fold.compiled.bytes`. -/

namespace Verified.Examples.FoldFile

file_theorems fold Fold.compiled "../../build/verified/fold.wasm" from Fold.compiled.bytes

end Verified.Examples.FoldFile
