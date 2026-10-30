import Library.Numerics.Arithmetic.CeilSqrt.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libceilsqrt.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.CeilSqrt.File

file_theorems libceilsqrt compiled "../../../../build/verified/libceilsqrt.wasm" from compiled.bytes

end Library.Numerics.Arithmetic.CeilSqrt.File
