module

public import Verified.Examples.Enums
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/enums.wasm`: the file holds
`encode Enums.compiled.module`, and it decodes to the module of `Enums.compiled.bytes`. -/

namespace Verified.Examples.EnumsFile

file_theorems enums Enums.compiled "../../build/verified/enums.wasm" from Enums.compiled.bytes

end Verified.Examples.EnumsFile
