import Library.Numerics.Float64.Lgamma.LgammaBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/lgamma.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Lgamma/LgammaFile.lean`: the file holds
`encode Lgamma.compiled.module`, which `Lgamma.compiled.encoded` states as literal bytes, so it
decodes to the module of `LgammaBytes.lgamma_bytes_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Lgamma.LgammaFile

file_theorems lgamma Lgamma.compiled "../../../../build/verified/lgamma.wasm"
  from LgammaBytes.lgamma_bytes_accuracy

end Library.Numerics.Float64.Lgamma.LgammaFile
