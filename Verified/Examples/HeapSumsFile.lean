import Verified.Examples.HeapSums
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/heapsums.wasm`: the file holds
`encode HeapSums.compiled.module`, and it decodes to the module of `HeapSums.compiled.bytes`. -/

namespace Verified.Examples.HeapSumsFile

file_theorems heapsums HeapSums.compiled "../../build/verified/heapsums.wasm"
  from HeapSums.compiled.bytes

end Verified.Examples.HeapSumsFile
