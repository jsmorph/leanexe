import Verified.Examples.TreeCore
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/treecore.wasm`: the file holds
`encode TreeCore.module`, and it decodes to `TreeCore.module`, which has no bytes theorem. -/

namespace Verified.Examples.TreeCoreFile

file_theorems treecore TreeCore "../../build/verified/treecore.wasm"

end Verified.Examples.TreeCoreFile
