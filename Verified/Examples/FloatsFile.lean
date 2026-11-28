module

public import Verified.Examples.Floats
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/floats.wasm`: the file holds
`encode Floats.compiled.module`, and it decodes to the module of `Floats.compiled.bytes`. -/

namespace Verified.Examples.FloatsFile

file_theorems floats Floats.compiled "../../build/verified/floats.wasm" from Floats.compiled.bytes

end Verified.Examples.FloatsFile
