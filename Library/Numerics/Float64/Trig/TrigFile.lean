import Library.Numerics.Float64.Trig.TrigTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/trig.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Trig/TrigFile.lean`: the file holds
`encode Trig.compiled.module`, so it decodes to the module of `TrigTheorem.sin_bytes_accuracy`
and `TrigTheorem.cos_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Trig.TrigFile

file_theorems trig Trig.compiled "../../../../build/verified/trig.wasm"
  from TrigTheorem.sin_bytes_accuracy, TrigTheorem.cos_bytes_accuracy

end Library.Numerics.Float64.Trig.TrigFile
