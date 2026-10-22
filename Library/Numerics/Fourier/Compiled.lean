import Library.Numerics.Fourier.Program
import Verified.Reflect.Command

namespace Library.Numerics.Fourier

verified_compile compiled := [Library.Numerics.Float64.Trig.kernelSin, Library.Numerics.Float64.Trig.kernelCos, Library.Numerics.Float64.Trig.remSmall, Library.Numerics.Float64.Trig.remMedium,
  Library.Numerics.Float64.Trig.mul64, Library.Numerics.Float64.Trig.clz64, Library.Numerics.Float64.Trig.window, Library.Numerics.Float64.Trig.mulTop, Library.Numerics.Float64.Trig.shiftTop, Library.Numerics.Float64.Trig.remLarge, Library.Numerics.Float64.Trig.remPio2,
  Library.Numerics.Float64.Trig.sinWith, Library.Numerics.Float64.Trig.cosWith, twiddleWith, transformWith, dftWith, inverseWith, powerSpectrumWith,
  twiddle, dft, inverse, powerSpectrum]

end Library.Numerics.Fourier
