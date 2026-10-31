import Library.Numerics.MultiPrecision.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/multiPrecision.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.MultiPrecision.File

file_theorems multiPrecision compiled "../../../build/verified/multiPrecision.wasm" from compiled.bytes

end Library.Numerics.MultiPrecision.File
