import LeanExe.Examples.Gpt
import Project.Compiler.Command

namespace Project.Gpt

open LeanExe.Examples.Gpt in
leanexe_compile gpt := [dot, matVec, layerNorm]

end Project.Gpt
