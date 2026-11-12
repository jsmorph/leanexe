import Demos.Gate.AssignmentVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/assignment.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Gate/AssignmentFile.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Gate.Assignment.File

open Demos.Gate.Assignment

file_theorems assignment compiled "../../build/verified/assignment.wasm" from compiled.bytes

end Demos.Gate.Assignment.File
