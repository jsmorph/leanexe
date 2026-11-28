module

public import Demos.Conjunction.AccuracyVerified
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/accuracy.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Conjunction/AccuracyFile.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Conjunction.Accuracy.File

open Demos.Conjunction.Accuracy

file_theorems accuracy compiled "../../build/verified/accuracy.wasm" from compiled.bytes

end Demos.Conjunction.Accuracy.File
