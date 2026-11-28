module

public import Verified.Examples.TailCore
public import LeanExe.Pipeline.FileBytes
import all Init.Data.Nat.Fold

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/tailcore.wasm`: the file holds
`encode TailCore.module`, and it decodes to `TailCore.module`, which has no bytes theorem. -/

namespace Verified.Examples.TailCoreFile

file_theorems tailcore TailCore "../../build/verified/tailcore.wasm"

end Verified.Examples.TailCoreFile
