import Demos.Gpt.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `Emit.lean` writes `build/gpt/gpt.wasm`, with
`lake env lean Demos/Gpt/File.lean`: the file holds the bytes of `gpt_bytes`, and it decodes to
`gpt.module`. -/

namespace Demos.Gpt

file_theorems gpt gpt "../../build/gpt/gpt.wasm"

end Demos.Gpt
