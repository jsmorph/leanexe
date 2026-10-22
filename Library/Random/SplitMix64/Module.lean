import Library.Random.SplitMix64.Program
import LeanExe.Compiler.Command

namespace Library.Random.SplitMix64

open Library.Random.SplitMix64

leanexe_compile prng := [splitMix, unitFloat]

end Library.Random.SplitMix64
