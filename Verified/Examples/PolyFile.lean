module

public import Verified.Examples.Poly
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/poly.wasm`: the file holds
`encode Poly.compiled.module`, and it decodes to the module of `Poly.compiled.bytes`. -/

namespace Verified.Examples.PolyFile

file_theorems poly Poly.compiled "../../build/verified/poly.wasm" from Poly.compiled.bytes

end Verified.Examples.PolyFile
