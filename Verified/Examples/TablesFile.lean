import Verified.Examples.Tables
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tables.wasm`: the file holds
`encode Tables.compiled.module`, and it decodes to the module of `Tables.compiled.bytes`. -/

namespace Verified.Examples.TablesFile

file_theorems tables Tables.compiled "../../build/verified/tables.wasm" from Tables.compiled.bytes

end Verified.Examples.TablesFile
