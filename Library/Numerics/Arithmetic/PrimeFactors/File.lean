module

public import Library.Numerics.Arithmetic.PrimeFactors.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/primeFactors.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.PrimeFactors.File

file_theorems primeFactors compiled "../../../../build/verified/primeFactors.wasm"
  from compiled.bytes

end Library.Numerics.Arithmetic.PrimeFactors.File
