import Verified.Examples.FourierExtraBytes
import LeanExe.Pipeline.FileBytes

namespace Verified.Examples.FourierFile

set_option maxRecDepth 100000 in
theorem fourier_file :
    Wasm.Encoding.encode Fourier.compiled.module =
      .ok (binary_file% "../../build/verified/fourier.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by decide +kernel)

theorem fourier_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/fourier.wasm") =
      .ok Fourier.compiled.module := by
  obtain ⟨⟨bytes, henc, hdec, _⟩, _, _⟩ := FourierExtraBytes.fourier_module_accuracy
  have h : binary_file% "../../build/verified/fourier.wasm" = bytes :=
    Except.ok.inj (fourier_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms fourier_file
#print axioms fourier_file_decode

end Verified.Examples.FourierFile
