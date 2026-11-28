module

public import Demos.Gate.Verified
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/chisquare.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Gate/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Gate.File

open Demos.Gate

file_theorems chisquare compiled "../../build/verified/chisquare.wasm" from compiled.bytes

end Demos.Gate.File
