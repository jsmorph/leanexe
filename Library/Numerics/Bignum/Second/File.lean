module

public import Library.Numerics.Bignum.Second.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/bignum2.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Bignum.Second.File

file_theorems bignum2 compiled "../../../../build/verified/bignum2.wasm" from compiled.bytes

end Library.Numerics.Bignum.Second.File
