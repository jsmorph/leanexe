import Demos.Gate.GateVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/gate.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Gate/GateFile.lean`: the file holds
`encode gateCompiled.module`, and it decodes to the module of `gateCompiled.bytes`. -/

namespace Demos.Gate.GateFile

open Demos.Gate

file_theorems gate gateCompiled "../../build/verified/gate.wasm" from gateCompiled.bytes

end Demos.Gate.GateFile
