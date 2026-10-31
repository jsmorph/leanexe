import Examples.Grids.Flat
import Verified.Reflect.Command

/-! The verified compiler's module of the functions of `Program.lean`, with the representations
of `Flat.lean`.  The reads, the counts, and `totalDensity` allocate nothing,
so their generated `implements` theorems state that they return without a trap.  `scaled`,
`ramp`, and `flags` build an array each, and `compiled.scaled.trapFree` and the others exclude
a trap when `top` can rise by the function's bound. -/

namespace Examples.Grids

verified_compile compiled := [density, pressure, indexAt, okAt, count, energySum, isGas, flagAt,
  flagCount, massAt, scaled, ramp, flags, totalDensity]

end Examples.Grids
