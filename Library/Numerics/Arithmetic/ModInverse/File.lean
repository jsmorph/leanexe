module

public import Library.Numerics.Arithmetic.ModInverse.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/modInverse.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Arithmetic.ModInverse.File

file_theorems modInverse compiled "../../../../build/verified/modInverse.wasm" from compiled.bytes

end Library.Numerics.Arithmetic.ModInverse.File
