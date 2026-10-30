import Library.Numerics.Float64.Sinpi.SinpiTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/sinpi.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Sinpi/SinpiFile.lean`: the file holds
`encode Sinpi.compiled.module`, so it decodes to the module of
`SinpiTheorem.sinpi_bytes_accuracy`, `SinpiTheorem.cospi_bytes_accuracy`, and
`SinpiTheorem.tanpi_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Sinpi.SinpiFile

file_theorems sinpi Sinpi.compiled "../../../../build/verified/sinpi.wasm"
  from SinpiTheorem.sinpi_bytes_accuracy, SinpiTheorem.cospi_bytes_accuracy,
    SinpiTheorem.tanpi_bytes_accuracy

end Library.Numerics.Float64.Sinpi.SinpiFile
