import Library.Numerics.Arithmetic.Sieve.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sieve.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.Sieve.File

file_theorems sieve compiled "../../../../build/verified/sieve.wasm" from compiled.bytes

end Library.Numerics.Arithmetic.Sieve.File
