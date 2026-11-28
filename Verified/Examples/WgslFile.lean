module

public import Verified.Examples.Wgsl
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/wgsl.wasm`: the file holds
`encode Wgsl.compiled.module`, and it decodes to the module of `Wgsl.compiled.bytes`. -/

namespace Verified.Examples.WgslFile

file_theorems wgsl Wgsl.compiled "../../build/verified/wgsl.wasm" from Wgsl.compiled.bytes

end Verified.Examples.WgslFile
