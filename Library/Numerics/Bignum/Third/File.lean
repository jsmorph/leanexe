module

public import Library.Numerics.Bignum.Third.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/bignum3.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Bignum.Third.File

file_theorems bignum3 compiled "../../../../build/verified/bignum3.wasm" from compiled.bytes

end Library.Numerics.Bignum.Third.File
