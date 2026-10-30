import Verified.Examples.Poly
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/poly.wasm`: the file holds
`encode Poly.compiled.module`, and it decodes to the module of `Poly.compiled.bytes`. -/

namespace Verified.Examples.PolyFile

file_theorems poly Poly.compiled "../../build/verified/poly.wasm" from Poly.compiled.bytes

end Verified.Examples.PolyFile
