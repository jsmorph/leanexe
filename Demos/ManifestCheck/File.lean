module

public import Demos.ManifestCheck.Compiled
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/manifestCheck.wasm`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.ManifestCheck.File

open Demos.ManifestCheck

file_theorems manifestCheck compiled "../../build/verified/manifestCheck.wasm" from compiled.bytes

end Demos.ManifestCheck.File
