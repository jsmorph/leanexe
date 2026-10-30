import Library.Numerics.Float64.Tgamma.TgammaBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tgamma.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Tgamma/TgammaFile.lean`: the file holds
`encode Tgamma.compiled.module`, which `Tgamma.compiled.encoded` states as literal bytes, so it
decodes to the module of `TgammaBytes.tgamma_bytes_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Tgamma.TgammaFile

file_theorems tgamma Tgamma.compiled "../../../../build/verified/tgamma.wasm"
  from TgammaBytes.tgamma_bytes_accuracy

end Library.Numerics.Float64.Tgamma.TgammaFile
