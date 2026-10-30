import Library.Numerics.Float64.Erfc.ErfcBytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/erfc.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Erfc/ErfcFile.lean`: the file holds
`encode Erfc.compiled.module`, which `Erfc.compiled.encoded` states as literal bytes, so it
decodes to the module of `ErfcBytes.erfc_bytes_accuracy`.  The file's bytes are a term nested
as deep as the file is long, which the kernel checks under a raised `maxRecDepth`. -/

namespace Library.Numerics.Float64.Erfc.ErfcFile

file_theorems erfc Erfc.compiled "../../../../build/verified/erfc.wasm"
  from ErfcBytes.erfc_bytes_accuracy

end Library.Numerics.Float64.Erfc.ErfcFile
