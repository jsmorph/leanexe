import Demos.Screening.Verified
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/screening.wasm`, with
`tools/leanrun --timeout 10m lake env lean Demos/Screening/File.lean`: the file holds
`encode compiled.module`, and it decodes to the module of `compiled.bytes`. -/

namespace Demos.Screening.File

open Demos.Screening

file_theorems screening compiled "../../build/verified/screening.wasm" from compiled.bytes

end Demos.Screening.File
