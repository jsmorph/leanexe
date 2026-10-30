import Verified.Examples.TailConditions
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/tailconditions.wasm`: the file
holds `encode TailConditions.compiled.module`, and it decodes to the module of
`TailConditions.compiled.bytes`. -/

namespace Verified.Examples.TailConditionsFile

file_theorems tailconditions TailConditions.compiled "../../build/verified/tailconditions.wasm"
  from TailConditions.compiled.bytes

end Verified.Examples.TailConditionsFile
