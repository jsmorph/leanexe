import Verified.Examples.OwnedTuples
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/ownedtuples.wasm`: the file holds
`encode OwnedTuples.module`, and it decodes to `OwnedTuples.module`, which has no bytes theorem. -/

namespace Verified.Examples.OwnedTuplesFile

file_theorems ownedtuples OwnedTuples "../../build/verified/ownedtuples.wasm"

end Verified.Examples.OwnedTuplesFile
