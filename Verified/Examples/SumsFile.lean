module

public import Verified.Examples.Sums
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/sums.wasm`: the file holds
`encode Sums.compiled.module`, and it decodes to the module of `Sums.compiled.bytes`. -/

namespace Verified.Examples.SumsFile

file_theorems sums Sums.compiled "../../build/verified/sums.wasm" from Sums.compiled.bytes

end Verified.Examples.SumsFile
