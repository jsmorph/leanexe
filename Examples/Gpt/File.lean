import Examples.Gpt.Bytes
import LeanExe.Pipeline.FileBytes

/-! Checked after `Emit.lean` writes `build/gpt/gpt.wasm`, with
`lake env lean Examples/Gpt/File.lean`: the file holds the bytes of `gpt_bytes`.  The
kernel compares the bytes as lists, since it reads an array element by walking the list
that represents the array. -/

namespace Examples.Gpt

theorem encode_eq_of_toList {m : Wasm.Module} {file : ByteArray}
    (h : (Wasm.Encoding.encode m).toOption.map (·.data.toList) = some file.data.toList) :
    Wasm.Encoding.encode m = .ok file := by
  cases hEncode : Wasm.Encoding.encode m with
  | error _ => simp [hEncode, Except.toOption] at h
  | ok bytes =>
    simp only [hEncode, Except.toOption, Option.map_some, Option.some.injEq] at h
    rw [ByteArray.ext (Array.toList_inj.mp h)]

set_option maxRecDepth 100000 in
/-- `build/gpt/gpt.wasm` holds `encode gpt.module`, so it decodes to `gpt.module`, whose
exports compute the GPT functions exactly (`gpt_bytes`). -/
theorem gpt_file :
    Wasm.Encoding.encode gpt.module = .ok (binary_file% "../../build/gpt/gpt.wasm") :=
  encode_eq_of_toList (by decide +kernel)

end Examples.Gpt
