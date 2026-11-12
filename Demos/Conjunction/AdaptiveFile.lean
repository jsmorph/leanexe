import Demos.Conjunction.AdaptiveVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/adaptive.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Conjunction/AdaptiveFile.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Conjunction.Adaptive.File

open Demos.Conjunction.Adaptive

file_theorems adaptive compiled "../../build/verified/adaptive.wasm" from compiled.bytes

end Demos.Conjunction.Adaptive.File
