module

public import Verified.Examples.Patterns
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/patterns.wasm`: the file holds
`encode Patterns.compiled.module`, and it decodes to the module of `Patterns.compiled.bytes`. -/

namespace Verified.Examples.PatternsFile

file_theorems patterns Patterns.compiled "../../build/verified/patterns.wasm"
  from Patterns.compiled.bytes

end Verified.Examples.PatternsFile
