import Library.Numerics.Float64.Trig.TrigTheorem
import LeanExe.Pipeline.FileBytes

/-! Checked after `tests/verified/run.sh` writes `build/verified/trig.wasm`, with
`tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Trig/TrigFile.lean`: the file holds
`encode Trig.compiled.module`, so it decodes to the module of `TrigTheorem.sin_bytes_accuracy`
and `TrigTheorem.cos_bytes_accuracy`. -/

namespace Library.Numerics.Float64.Trig.TrigFile

set_option maxRecDepth 100000 in
/-- `build/verified/trig.wasm` holds `encode Trig.compiled.module`. -/
theorem trig_file :
    Wasm.Encoding.encode Trig.compiled.module =
      .ok (binary_file% "../../../../build/verified/trig.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

/-- `build/verified/trig.wasm` decodes to the module of `TrigTheorem.sin_bytes_accuracy` and
`TrigTheorem.cos_bytes_accuracy`.  The proof takes the bytes from both theorems together, so its
axiom report covers both. -/
theorem trig_file_decode :
    Wasm.Encoding.decode (binary_file% "../../../../build/verified/trig.wasm") =
      .ok Trig.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _⟩ :=
    And.intro TrigTheorem.sin_bytes_accuracy TrigTheorem.cos_bytes_accuracy
  have h : binary_file% "../../../../build/verified/trig.wasm" = bytes :=
    Except.ok.inj (trig_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms trig_file
#print axioms trig_file_decode

end Library.Numerics.Float64.Trig.TrigFile
