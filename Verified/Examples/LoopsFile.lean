module

public import Verified.Examples.Loops
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/loops.wasm`: the file holds
`encode Loops.compiled.module`, and it decodes to the module of `Loops.compiled.bytes`. -/

namespace Verified.Examples.LoopsFile

file_theorems loops Loops.compiled "../../build/verified/loops.wasm" from Loops.compiled.bytes

end Verified.Examples.LoopsFile
