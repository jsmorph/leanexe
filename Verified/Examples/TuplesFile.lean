module

public import Verified.Examples.Tuples
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/tuples.wasm`: the file holds
`encode Tuples.module`, and it decodes to `Tuples.module`, which has no bytes theorem. -/

namespace Verified.Examples.TuplesFile

file_theorems tuples Tuples "../../build/verified/tuples.wasm"

end Verified.Examples.TuplesFile
