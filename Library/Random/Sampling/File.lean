import Library.Random.Sampling.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sampling.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Random.Sampling.File

file_theorems sampling compiled "../../../build/verified/sampling.wasm" from compiled.bytes

end Library.Random.Sampling.File
