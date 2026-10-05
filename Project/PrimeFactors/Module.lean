import LeanExe.Examples.PrimeFactors
import Project.Compiler.Command

namespace Project.PrimeFactors

open LeanExe.Examples.PrimeFactors

leanexe_compile primeFactors := [countFactors, compute]

end Project.PrimeFactors
