import Library.Numerics.Arithmetic.PrimeFactors.Compiled
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/primeFactors.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.PrimeFactors.File

file_theorems primeFactors compiled "../../../../build/verified/primeFactors.wasm"
  from compiled.bytes

end Library.Numerics.Arithmetic.PrimeFactors.File
