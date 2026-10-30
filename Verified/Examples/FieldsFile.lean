import Verified.Examples.Fields
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/fields.wasm`: the file holds
`encode Fields.compiled.module`, and it decodes to the module of `Fields.compiled.bytes`. -/

namespace Verified.Examples.FieldsFile

file_theorems fields Fields.compiled "../../build/verified/fields.wasm" from Fields.compiled.bytes

end Verified.Examples.FieldsFile
