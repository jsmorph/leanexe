import Verified.Examples.Select
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/select.wasm`: the file holds
`encode Select.compiled.module`, and it decodes to the module of `Select.compiled.bytes`. -/

namespace Verified.Examples.SelectFile

file_theorems select Select.compiled "../../build/verified/select.wasm" from Select.compiled.bytes

end Verified.Examples.SelectFile
