import Library.Arrays.MaxSegmentSum.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libmss.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Arrays.MaxSegmentSum.File

file_theorems libmss compiled "../../../build/verified/libmss.wasm" from compiled.bytes

end Library.Arrays.MaxSegmentSum.File
