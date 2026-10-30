import Verified.Examples.Records
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/records.wasm`: the file holds
`encode Records.compiled.module`, and it decodes to the module of `Records.compiled.bytes`. -/

namespace Verified.Examples.RecordsFile

file_theorems records Records.compiled "../../build/verified/records.wasm"
  from Records.compiled.bytes

end Verified.Examples.RecordsFile
