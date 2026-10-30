import Library.Random.Xorshift.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/xorshift.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Random.Xorshift.File

file_theorems xorshift compiled "../../../build/verified/xorshift.wasm" from compiled.bytes

end Library.Random.Xorshift.File
