import Verified.Examples.Pairs
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/pairs.wasm`: the file holds
`encode Pairs.compiled.module`, and it decodes to the module of `Pairs.compiled.bytes`. -/

namespace Verified.Examples.PairsFile

file_theorems pairs Pairs.compiled "../../build/verified/pairs.wasm" from Pairs.compiled.bytes

end Verified.Examples.PairsFile
