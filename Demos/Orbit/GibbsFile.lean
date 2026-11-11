import Demos.Orbit.GibbsVerified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/gibbs.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Orbit/GibbsFile.lean`: the file holds
`encode gibbsCompiled.module`, and it decodes to the module of `gibbsCompiled.bytes`. -/

namespace Demos.Orbit.GibbsFile

open Demos.Orbit

file_theorems gibbs gibbsCompiled "../../build/verified/gibbs.wasm" from gibbsCompiled.bytes

end Demos.Orbit.GibbsFile
