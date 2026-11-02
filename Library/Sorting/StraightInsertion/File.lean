import Library.Sorting.StraightInsertion.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/straightInsertion.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Sorting.StraightInsertion.File

file_theorems straightInsertion compiled "../../../build/verified/straightInsertion.wasm"
  from compiled.bytes

end Library.Sorting.StraightInsertion.File
