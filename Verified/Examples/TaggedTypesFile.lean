module

public import Verified.Examples.TaggedTypes
public import LeanExe.Pipeline.FileBytes

@[expose] public section

/-! Checked after `tests/verified/run.sh` writes `build/verified/taggedtypes.wasm`: the file holds
`encode TaggedTypes.compiled.module`, and it decodes to the module of `TaggedTypes.compiled.bytes`.
-/

namespace Verified.Examples.TaggedTypesFile

file_theorems taggedtypes TaggedTypes.compiled "../../build/verified/taggedtypes.wasm"
  from TaggedTypes.compiled.bytes

end Verified.Examples.TaggedTypesFile
