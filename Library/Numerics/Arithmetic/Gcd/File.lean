import Library.Numerics.Arithmetic.Gcd.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/gcd.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.Gcd.File

file_theorems gcd compiled "../../../../build/verified/gcd.wasm" from compiled.bytes

end Library.Numerics.Arithmetic.Gcd.File
