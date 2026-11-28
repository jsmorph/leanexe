module

public import Library.Numerics.Statistics.Mean.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/mean.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Numerics.Statistics.Mean.File

file_theorems mean compiled "../../../../build/verified/mean.wasm" from compiled.bytes

end Library.Numerics.Statistics.Mean.File
