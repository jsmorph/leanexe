import Library.HashTables.LinearProbing.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/hashTable.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.HashTables.LinearProbing.File

file_theorems hashTable compiled "../../../build/verified/hashTable.wasm" from compiled.bytes

end Library.HashTables.LinearProbing.File
