import Verified.Examples.Arrays
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/arrays.wasm`: the file holds
`encode Arrays.compiled.module`, and it decodes to the module of `Arrays.compiled.bytes`. -/

namespace Verified.Examples.ArraysFile

file_theorems arrays Arrays.compiled "../../build/verified/arrays.wasm" from Arrays.compiled.bytes

end Verified.Examples.ArraysFile
