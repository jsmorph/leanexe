import Demos.Orbit.LambertVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/lambert.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Orbit/LambertFile.lean`: the file holds
`encode lambertCompiled.module`, and it decodes to the module of `lambertCompiled.bytes`. -/

namespace Demos.Orbit.LambertFile

open Demos.Orbit

file_theorems lambert lambertCompiled "../../build/verified/lambert.wasm"
  from lambertCompiled.bytes

end Demos.Orbit.LambertFile
