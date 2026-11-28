module

public import Library.Numerics.Limiters.Minmod.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/libminmod.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Limiters.Minmod.File

file_theorems libminmod compiled "../../../../build/verified/libminmod.wasm" from compiled.bytes

end Library.Numerics.Limiters.Minmod.File
