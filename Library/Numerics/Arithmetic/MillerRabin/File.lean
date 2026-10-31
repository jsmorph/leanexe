import Library.Numerics.Arithmetic.MillerRabin.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/millerRabin.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.MillerRabin.File

file_theorems millerRabin compiled "../../../../build/verified/millerRabin.wasm" from compiled.bytes

end Library.Numerics.Arithmetic.MillerRabin.File
