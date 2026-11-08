import Verified.Examples.Signed
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/signed.wasm`: the file holds
`encode Signed.compiled.module`, and it decodes to the module of `Signed.compiled.bytes`. -/

namespace Verified.Examples.SignedFile

file_theorems signed Signed.compiled "../../build/verified/signed.wasm"
  from Signed.compiled.bytes

end Verified.Examples.SignedFile
