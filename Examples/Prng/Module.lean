import Examples.Prng.Program
import LeanExe.Compiler.Command

namespace Examples.Prng

open Examples.Prng

leanexe_compile prng := [splitMix, unitFloat]

end Examples.Prng
