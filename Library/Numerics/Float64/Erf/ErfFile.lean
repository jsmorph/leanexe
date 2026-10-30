import Library.Numerics.Float64.Erf.ErfTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/erf.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Erf/ErfFile.lean`: the file holds
`encode Erf.compiled.module`, so it decodes to the module of `ErfTheorem.erf_module_accuracy`,
which depends on every byte theorem of the module. -/

namespace Library.Numerics.Float64.Erf.ErfFile

file_theorems erf Erf.compiled "../../../../build/verified/erf.wasm"
  from ErfTheorem.erf_module_accuracy

end Library.Numerics.Float64.Erf.ErfFile
