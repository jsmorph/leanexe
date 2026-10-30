import Examples.Bucket.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/bucket.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Examples.Bucket.File

file_theorems bucket compiled "../../build/verified/bucket.wasm" from compiled.bytes

end Examples.Bucket.File
