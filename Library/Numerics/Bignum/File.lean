module

public import Library.Numerics.Bignum.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/bignum.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Bignum.File

file_theorems bignum compiled "../../../build/verified/bignum.wasm" from compiled.bytes

end Library.Numerics.Bignum.File
