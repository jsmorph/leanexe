module

public import Library.Numerics.Filters.Cic.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/libcic.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Filters.Cic.File

file_theorems libcic compiled "../../../../build/verified/libcic.wasm" from compiled.bytes

end Library.Numerics.Filters.Cic.File
