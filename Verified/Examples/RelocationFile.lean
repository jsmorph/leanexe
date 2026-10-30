import Verified.Examples.Relocation
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/relocation.wasm`: the file holds
`encode Relocation.module`, and it decodes to `Relocation.module`, which has no bytes theorem. -/

namespace Verified.Examples.RelocationFile

file_theorems relocation Relocation "../../build/verified/relocation.wasm"

end Verified.Examples.RelocationFile
