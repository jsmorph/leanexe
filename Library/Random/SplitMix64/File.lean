import Library.Random.SplitMix64.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/prng.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Random.SplitMix64.File

file_theorems prng compiled "../../../build/verified/prng.wasm" from compiled.bytes

end Library.Random.SplitMix64.File
