import Demos.Slew.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/slew.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Slew/File.lean`: the file holds
`encode compiled.module`, which `compiled.encoded` states as literal bytes, so it decodes to the
module whose `plan` export `compiled.plan.implements` describes.  The file's bytes are a term
nested as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Demos.Slew.File

open Demos.Slew.Verified

file_theorems slew compiled "../../build/verified/slew.wasm" from compiled.bytes

end Demos.Slew.File
