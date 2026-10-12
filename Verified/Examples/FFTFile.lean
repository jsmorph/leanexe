import Verified.Examples.FFTBytes
import LeanExe.Pipeline.FileBytes

namespace Verified.Examples.FFTFile

set_option maxRecDepth 100000 in
theorem fft_file :
    Wasm.Encoding.encode FFT.compiled.module =
      .ok (binary_file% "../../build/verified/fft.wasm") :=
  LeanExe.Pipeline.encode_eq_of_toList (by
    rw [FFT.compiled.module_literal_eq]
    decide +kernel)

set_option maxRecDepth 100000 in
theorem fft_file_decode :
    Wasm.Encoding.decode (binary_file% "../../build/verified/fft.wasm") =
      .ok FFT.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := FFTBytes.fft_module_accuracy
  have h : binary_file% "../../build/verified/fft.wasm" = bytes :=
    Except.ok.inj (fft_file.symm.trans henc)
  rw [h]
  exact hdec

#print axioms fft_file
#print axioms fft_file_decode

end Verified.Examples.FFTFile
