import Library.Numerics.Arithmetic.BinaryGcd.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/binaryGcd.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.BinaryGcd.File

file_theorems binaryGcd compiled "../../../../build/verified/binaryGcd.wasm" from compiled.bytes

end Library.Numerics.Arithmetic.BinaryGcd.File
