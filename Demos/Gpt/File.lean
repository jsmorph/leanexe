import Demos.Gpt.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `Emit.lean` writes `build/gpt/gpt.wasm`, with
`lake env lean Demos/Gpt/File.lean`: the file holds the bytes of `gpt_bytes`. -/

namespace Demos.Gpt

set_option maxRecDepth 100000 in
/-- `build/gpt/gpt.wasm` holds `encode gpt.module`, so it decodes to `gpt.module`, whose
exports compute the GPT functions exactly (`gpt_bytes`). -/
theorem gpt_file :
    Wasm.Encoding.encode gpt.module = .ok (binary_file% "../../build/gpt/gpt.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

end Demos.Gpt
