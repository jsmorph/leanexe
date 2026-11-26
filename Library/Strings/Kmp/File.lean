module

public import Library.Strings.Kmp.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/kmp.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Library.Strings.Kmp.File

file_theorems kmp compiled "../../../build/verified/kmp.wasm" from compiled.bytes

end Library.Strings.Kmp.File
