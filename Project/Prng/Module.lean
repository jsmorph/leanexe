import LeanExe.Examples.Prng
import Project.Compiler.Command

namespace Project.Prng

open LeanExe.Examples.Prng

leanexe_compile prng := [splitMix, unitFloat]

end Project.Prng
