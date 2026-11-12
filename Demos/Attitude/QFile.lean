import Demos.Attitude.QVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh --cases qmethod` writes `build/verified/qmethod.wasm`,
with `tools/leanrun --timeout 10m lake env lean Demos/Attitude/QFile.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Attitude.QMethod.File

open Demos.Attitude.QMethod

file_theorems qmethod compiled "../../build/verified/qmethod.wasm" from compiled.bytes

end Demos.Attitude.QMethod.File
