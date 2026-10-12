import Verified.Examples.FFT

namespace Verified.Examples.FFT

local instance : LeanExe.Pipeline.Represent (Array (Float × Float)) :=
  Elem.wordsInst (.prod .float .float)

set_option Verified.Reflect.materializeModule true in
verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Trig.remSmall, Trig.remMedium,
  Trig.mul64, Trig.clz64, Trig.window, Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2,
  Trig.sinWith, Trig.cosWith, Fourier.twiddleWith, Fourier.transformWith,
  isRadix2, stageCount, reverseBits, copyReversed, stageWith, radix2With, fftTransformWith,
  fftWith, inverseWith, powerSpectrumWith, fft, inverse, powerSpectrum]

#print axioms compiled.fft.implements
#print axioms compiled.inverse.implements
#print axioms compiled.powerSpectrum.implements
#print axioms compiled.module_literal_eq
#print axioms compiled.bytes

end Verified.Examples.FFT
