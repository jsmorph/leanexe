module

public import Library.Numerics.Decimal.Int64Text.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/int64Text.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Decimal.Int64Text.File

file_theorems int64Text compiled "../../../../build/verified/int64Text.wasm" from compiled.bytes

end Library.Numerics.Decimal.Int64Text.File
