module

public import Demos.BignumCalc.MessageCompiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/bignumCalc.wasm`: the file holds
`encode messageCompiled.module`, and it decodes to the module of `messageCompiled.bytes`. -/

namespace Demos.BignumCalc.File

file_theorems bignumCalc messageCompiled "../../build/verified/bignumCalc.wasm" from messageCompiled.bytes

end Demos.BignumCalc.File
