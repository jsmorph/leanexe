module

public import Verified.Examples.Elements
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/elements.wasm`: the file holds
`encode Elements.compiled.module`, and it decodes to the module of `Elements.compiled.bytes`. -/

namespace Verified.Examples.ElementsFile

file_theorems elements Elements.compiled "../../build/verified/elements.wasm"
  from Elements.compiled.bytes

end Verified.Examples.ElementsFile
