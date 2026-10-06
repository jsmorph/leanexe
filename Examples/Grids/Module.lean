import Examples.Grids.Program
import LeanExe.Compiler.Command

namespace Examples.Grids

open Examples.Grids

leanexe_compile grids := [density, pressure, indexAt, okAt, count, energySum, isGas, flagAt,
  flagCount, massAt, scaled, ramp, flags,
  totalDensity]

end Examples.Grids
