import Examples.PrimeFactors.Program
import LeanExe.Compiler.Command

namespace Examples.PrimeFactors

open Examples.PrimeFactors

leanexe_compile primeFactors := [countFactors, compute]

end Examples.PrimeFactors
