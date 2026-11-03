import Library.Combinatorics.NextPermutation.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/nextPermutation.wasm`: the file
holds `encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Combinatorics.NextPermutation.File

file_theorems nextPermutation compiled "../../../build/verified/nextPermutation.wasm"
  from compiled.bytes

end Library.Combinatorics.NextPermutation.File
