import Library.Numerics.Interval.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/libinterval.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Interval.File

file_theorems libinterval compiled "../../../build/verified/libinterval.wasm" from compiled.bytes

end Library.Numerics.Interval.File
