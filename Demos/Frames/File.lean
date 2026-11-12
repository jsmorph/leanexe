import Demos.Frames.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/frames.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Frames/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Frames.File

open Demos.Frames

file_theorems frames compiled "../../build/verified/frames.wasm" from compiled.bytes

end Demos.Frames.File
